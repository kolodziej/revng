#pragma once

//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

#include <map>
#include <set>

#include "revng/EarlyFunctionAnalysis/CallGraph.h"
#include "revng/EarlyFunctionAnalysis/Common.h"
#include "revng/MFP/SetLattices.h"
#include "revng/Model/Register.h"
#include "revng/Support/MetaAddress.h"

#include "DetectABI.h"

namespace efa {

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

  DetectABI &DA;

  explicit UsedRegistersMFI(DetectABI &DA) : DA{ DA } {}

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
                                          DA.getBinary()->Architecture());
    };

    const auto &Addr = L->Address;
    if (Addr.isInvalid()) {
      return Result;
    }

    auto Results = DA.analyzeABI(Addr);
    for (auto &[CSV, State] : Results.ArgumentsRegisters) {
      if (State == abi::RegisterState::Yes) {
        Result.Map[Addr].ArgumentRegisters.insert(Reg(CSV));
      }
    }
    for (auto &[CSV, State] : Results.FinalReturnValuesRegisters) {
      if (State == abi::RegisterState::YesOrDead) {
        Result.Map[Addr].ReturnRegisters.insert(Reg(CSV));
      }
    }

    return Result;
  }
};

} // namespace efa
