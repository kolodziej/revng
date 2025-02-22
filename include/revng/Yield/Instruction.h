#pragma once

//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

#include <limits>
#include <string>

#include "revng/ADT/SortedVector.h"
#include "revng/Model/VerifyHelper.h"
#include "revng/Support/MetaAddress.h"
#include "revng/Support/MetaAddress/YAMLTraits.h"
#include "revng/Yield/TagType.h"

namespace yield {
using ByteContainer = llvm::SmallVector<uint8_t, 16>;
}

/* TUPLE-TREE-YAML

name: Instruction
type: struct
fields:
  - name: Address
    doc: >
      Indicates the address of the first byte of the instruction.
    type: MetaAddress
  - name: RawBytes
    type: yield::ByteContainer
  - name: Disassembled
    type: string

  - name: Tags
    sequence:
      type: SortedVector
      elementType: Tag
    optional: true

  - name: OpcodeIdentifier
    type: string
    optional: true
  - name: Comment
    doc: >
      Contains any extra information deduced based on the disassembly of this
      instruction that could be relevant for the user.
    type: string
    optional: true
  - name: Error
    doc: >
      Contains any extra extra warning/error style information deduced based on
      the disassembly of this instruction that could be relevant for the user.
    type: string
    optional: true

key:
  - Address

TUPLE-TREE-YAML */

#include "revng/Yield/Generated/Early/Instruction.h"

namespace yield {

class Instruction : public generated::Instruction {
public:
  using generated::Instruction::Instruction;

public:
  bool verify(model::VerifyHelper &VH) const;
  void dump() const debug_function;

public:
  inline bool verify() const debug_function { return verify(false); }
  inline bool verify(bool Assert) const debug_function {
    model::VerifyHelper VH(Assert);
    return verify(VH);
  }
};

} // namespace yield

#include "revng/Yield/Generated/Late/Instruction.h"
