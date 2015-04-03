set(LLVM_LINK_COMPONENTS ${LLVM_TARGETS_TO_BUILD} bitreader asmparser bitwriter irreader instrumentation scalaropts objcarcopts ipo vectorize)

add_llvm_tool(dppgen
  dppgen.cpp
  InstructionGraph.h
  InstructionGraph.cpp
  generatePartitionsUtil.h
  generateCInstruction.h
  generateCFunctions.h
  generatePartitions.h
  )
set_target_properties(dppgen PROPERTIES ENABLE_EXPORTS 1)
