

#include "revng/BasicAnalyses/GeneratedCodeBasicInfo.h"

class PreservedRegisters {
private:
  GeneratedCodeBasicInfo &GCBI;
public:
  using CSVVector = llvm::SmallVector<llvm::GlobalVariable *, 16>;

  explicit PreservedRegisters(GeneratedCodeBasicInfo &GCBI) : GCBI{GCBI} {}

  CSVVector abiCSVs

};
