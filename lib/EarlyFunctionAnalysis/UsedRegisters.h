#pragma once

//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

#include <map>
#include <set>

#include "revng/EarlyFunctionAnalysis/ABIAnalysis.h"
#include "revng/EarlyFunctionAnalysis/CallGraph.h"
#include "revng/EarlyFunctionAnalysis/Common.h"
#include "revng/EarlyFunctionAnalysis/CFGAnalyzer.h"
#include "revng/MFP/SetLattices.h"
#include "revng/Model/Register.h"
#include "revng/Support/MetaAddress.h"
#include "revng/Support/IRHelpers.h"

namespace efa {

static std::set<llvm::GlobalVariable *>
findWrittenRegisters(llvm::Function *F) {
  using namespace llvm;

  std::set<GlobalVariable *> WrittenRegisters;
  for (auto &BB : *F) {
    for (auto &I : BB) {
      if (auto *SI = dyn_cast<StoreInst>(&I)) {
        Value *Ptr = skipCasts(SI->getPointerOperand());
        if (auto *GV = dyn_cast<GlobalVariable>(Ptr))
          WrittenRegisters.insert(GV);
      }
    }
  }

  return WrittenRegisters;
}

static void
suppressCSAndSPRegisters(ABIAnalyses::ABIAnalysesResults &ABIResults,
                         const std::set<llvm::GlobalVariable *> &CalleeSavedRegs) {
  using RegisterState = abi::RegisterState::Values;

  // Suppress from arguments
  for (const auto &Reg : CalleeSavedRegs) {
    auto It = ABIResults.ArgumentsRegisters.find(Reg);
    if (It != ABIResults.ArgumentsRegisters.end())
      It->second = RegisterState::No;
  }

  // Suppress from return values
  for (const auto &[K, _] : ABIResults.ReturnValuesRegisters) {
    for (const auto &Reg : CalleeSavedRegs) {
      auto It = ABIResults.ReturnValuesRegisters[K].find(Reg);
      if (It != ABIResults.ReturnValuesRegisters[K].end())
        It->second = RegisterState::No;
    }
  }

  // Suppress from call-sites
  for (const auto &[K, _] : ABIResults.CallSites) {
    for (const auto &Reg : CalleeSavedRegs) {
      if (ABIResults.CallSites[K].ArgumentsRegisters.count(Reg) != 0)
        ABIResults.CallSites[K].ArgumentsRegisters[Reg] = RegisterState::No;

      if (ABIResults.CallSites[K].ReturnValuesRegisters.count(Reg) != 0)
        ABIResults.CallSites[K].ReturnValuesRegisters[Reg] = RegisterState::No;
    }
  }
}


struct FunctionABI {
  using SetOfRegisters = std::set<model::Register::Values>;
  using SUL = SetUnionLattice<SetOfRegisters>;
  SetOfRegisters ArgumentRegisters;
  SetOfRegisters ReturnRegisters;

  [[nodiscard]] FunctionABI combineValues(const FunctionABI &A2) const {
    FunctionABI Result{
      .ArgumentRegisters = SUL::combineValues(ArgumentRegisters,
                                              A2.ArgumentRegisters),
      .ReturnRegisters = SUL::combineValues(ReturnRegisters, A2.ReturnRegisters)
    };
    return Result;
  }

  [[nodiscard]] bool isLessOrEqual(const FunctionABI &Right) const {
    if (!SUL::isLessOrEqual(ArgumentRegisters, Right.ArgumentRegisters)) {
      return false;
    }

    return SUL::isLessOrEqual(ReturnRegisters, Right.ReturnRegisters);
  }
};

class LatticeElement {
public:
  using AddressABIMap = std::map<MetaAddress, FunctionABI>;
  using MapValue = AddressABIMap::value_type;
  AddressABIMap Map;

public:
  [[nodiscard]] std::optional<MapValue> find(MetaAddress Address) const {
    if (auto It = Map.find(Address); It != Map.end()) {
      return { *It };
    }

    return std::nullopt;
  }

  [[nodiscard]] bool
  hasReturnRegister(MetaAddress Address, model::Register::Values V) const {
    auto It = Map.find(Address);
    if (It != Map.end()) {
      return It->second.ReturnRegisters.count(V);
    }

    return false;
  }

  [[nodiscard]] bool
  hasArgumentRegister(MetaAddress Address, model::Register::Values V) const {
    auto It = Map.find(Address);
    if (It != Map.end()) {
      return It->second.ArgumentRegisters.count(V);
    }

    return false;
  }
};

struct UsedRegistersMFI {
  using Label = BasicBlockNode *;
  using GraphType = llvm::Inverse<BasicBlockNode *>;
  using LatticeElement = LatticeElement;

  using CSVSet = std::set<llvm::GlobalVariable *>;

  GeneratedCodeBasicInfo &GCBI;
  CFGAnalyzer &Analyzer;
  TupleTree<model::Binary> &Binary;
  FunctionSummaryOracle &Oracle;

  explicit UsedRegistersMFI(GeneratedCodeBasicInfo &GCBI,
                            CFGAnalyzer &Analyzer,
                            TupleTree<model::Binary> &Binary,
                            FunctionSummaryOracle &Oracle) :
    GCBI{ GCBI }, Analyzer{ Analyzer }, Binary{ Binary }, Oracle{ Oracle } {}

  [[nodiscard]] LatticeElement
  combineValues(const LatticeElement &E1, const LatticeElement &E2) const {
    LatticeElement Out;
    for (const auto &[Address, E1Abi] : E1.Map) {
      auto E2It = E2.Map.find(Address);
      if (E2It != E2.Map.end()) {
        Out.Map[Address] = E1Abi.combineValues(E2It->second);
      } else {
        Out.Map[Address] = E1Abi;
      }
    }

    for (const auto &[Address, E2Abi] : E2.Map) {
      auto It = Out.Map.find(Address);
      if (It != Out.Map.end()) {
        It->second = E2Abi;
      }
    }

    return Out;
  }

  [[nodiscard]] bool
  isLessOrEqual(const LatticeElement &Left, const LatticeElement &Right) const {
    for (const auto &[Address, LeftAbi] : Left.Map) {
      auto It = Right.Map.find(Address);
      if (It != Right.Map.end()) {
        if (!LeftAbi.isLessOrEqual(It->second)) {
          return false;
        }
      }
    }

    return true;
  }

  [[nodiscard]] LatticeElement
  applyTransferFunction(Label L, const LatticeElement &E2) const {
    LatticeElement Result = E2;
    auto Reg = [this](const llvm::GlobalVariable *V) {
      return model::Register::fromCSVName(V->getName(),
                                          Binary->Architecture());
    };

    const auto &Address = L->Address;
    if (Address.isInvalid()) {
      return Result;
    }

    auto Entry = GCBI.getBlockAt(Address);
    if (!Entry) {
      return Result; // WIP: don't know if that's correct; probably not!!
    }

    // Detect function boundaries
    OutlinedFunction OutlinedFunction = Analyzer.outline(Entry);

    // Find registers that may be target of at least one store. This helps
    // refine the final results.
    auto WrittenRegisters = findWrittenRegisters(
      OutlinedFunction.Function.get());

    using namespace ABIAnalyses;
    // Run ABI-independent data-flow analyses
    ABIAnalysesResults ABIResults;
    ABIResults = analyzeOutlinedFunction(OutlinedFunction.Function.get(),
                                         GCBI,
                                         Analyzer.preCallHook(),
                                         Analyzer.postCallHook(),
                                         Analyzer.retHook());
    const auto &Summary = Oracle.getLocalFunction(Address);
    auto CalleeSavedRegs = computePreservedCSVs(Summary.ClobberedRegisters);
    auto ActualCalleeSavedRegs = intersect(CalleeSavedRegs, WrittenRegisters);

    // Union between effective callee-saved registers and SP
    ActualCalleeSavedRegs.insert(GCBI.spReg());

    // Refine ABI analyses results by suppressing callee-saved and stack
    // pointer registers.
    suppressCSAndSPRegisters(ABIResults, ActualCalleeSavedRegs);

    // Merge return values registers
    ABIAnalyses::finalizeReturnValues(ABIResults);

    for (auto &[CSV, State] : ABIResults.ArgumentsRegisters) {
      if (State == abi::RegisterState::Yes) {
        Result.Map[Address].ArgumentRegisters.insert(Reg(CSV));
      }
    }
    for (auto &[CSV, State] : ABIResults.FinalReturnValuesRegisters) {
      if (State == abi::RegisterState::YesOrDead) {
        Result.Map[Address].ReturnRegisters.insert(Reg(CSV));
      }
    }

    return Result;
  }

  CSVSet computePreservedCSVs(const CSVSet &ClobberedRegisters) const {
    using llvm::GlobalVariable;
    using std::set;
    set<GlobalVariable *> PreservedRegisters(Analyzer.abiCSVs().begin(),
                                             Analyzer.abiCSVs().end());
    std::erase_if(PreservedRegisters, [&](const auto &E) {
      auto End = ClobberedRegisters.end();
      return ClobberedRegisters.find(E) != End;
    });

    return PreservedRegisters;
  }
};

} // namespace efa
