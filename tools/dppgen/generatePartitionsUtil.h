
#include "llvm/Support/IncludeFile.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Pass.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/raw_ostream.h"
#include "InstructionGraph.h"
using namespace llvm;
int instructionLatencyLookup(Instruction* ins)
{
    // normal instructions like "and, or , add, shift, are assigned a value of 3, multiply assigned a value of 10"
    // load and store assigned a value of 10, and 10 means one pipeline stage,
    if(ins->mayReadFromMemory())
        return 1;
    if(ins->getOpcode()==Instruction::Mul)
        return 5;
    if(ins->getOpcode()==Instruction::Br)
        return 0;
    return 1;
}
std::string replaceAllDotWUS(std::string original)
{
   std::replace( original.begin(), original.end(), '.', '_');

}


static std::string generateSingleStatement(Instruction* curIns, bool remoteSrc, bool remoteDst)
{
    // if it is remote src
    string a = "f";
    return a;
}

