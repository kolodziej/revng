#pragma once

//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

#include <array>
#include <string>

#include "llvm/ADT/ArrayRef.h"
#include "llvm/Support/raw_ostream.h"

#include "revng/Pipeline/Contract.h"
#include "revng/Pipeline/Target.h"
#include "revng/Pipes/FileContainer.h"
#include "revng/Pipes/FunctionStringMap.h"
#include "revng/Pipes/Kinds.h"
#include "revng/Pipes/StringBufferContainer.h"

namespace revng::pipes {

inline constexpr char CrossRelationsFileMIMEType[] = "application/"
                                                     "x.yaml.cross-relations";
inline constexpr char CrossRelationsFileSuffix[] = "";
inline constexpr char CrossRelationsName[] = "BinaryCrossRelations";

using CrossRelationsFileContainer = FileContainer<&kinds::BinaryCrossRelations,
                                                  CrossRelationsName,
                                                  CrossRelationsFileMIMEType,
                                                  CrossRelationsFileSuffix>;

inline constexpr char CallGraphSVGMIMEType[] = "image/svg";
inline constexpr char CallGraphSVGSuffix[] = ".svg";
inline constexpr char CallGraphSVGName[] = "CallGraphSVG";

using CallGraphSVGFileContainer = StringBufferContainer<&kinds::CallGraphSVG,
                                                        CallGraphSVGName,
                                                        CallGraphSVGMIMEType,
                                                        CallGraphSVGSuffix>;

inline constexpr char CallGraphSliceMIMEType[] = "image/svg";
inline constexpr char CallGraphSliceName[] = "CallGraphSliceSVG";

using CallGraphSliceSVGStringMap = FunctionStringMap<&kinds::CallGraphSliceSVG,
                                                     CallGraphSliceName,
                                                     CallGraphSliceMIMEType>;

class ProcessCallGraph {
public:
  static constexpr const auto Name = "ProcessCallGraph";

public:
  inline std::array<pipeline::ContractGroup, 1> getContract() const {
    return { pipeline::ContractGroup(kinds::IsolatedRoot,
                                     0,
                                     kinds::BinaryCrossRelations,
                                     1,
                                     pipeline::InputPreservation::Preserve) };
  }

public:
  void run(pipeline::Context &Context,
           const pipeline::LLVMContainer &TargetsList,
           CrossRelationsFileContainer &OutputFile);

  void print(const pipeline::Context &Ctx,
             llvm::raw_ostream &OS,
             llvm::ArrayRef<std::string> ContainerNames) const;
};

} // namespace revng::pipes
