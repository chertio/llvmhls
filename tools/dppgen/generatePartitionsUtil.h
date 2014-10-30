#ifndef GENPARTUTIL
#define GENPARTUTIL

#include "llvm/Support/IncludeFile.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Pass.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/raw_ostream.h"
#include "InstructionGraph.h"
#include "llvm/IR/Constants.h"
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
std::string int2Str(int in)
{

    std::ostringstream ss;
    ss << in;
    return ss.str();
}

std::string replaceAllDotWUS(std::string original)
{
   std::replace( original.begin(), original.end(), '.', '_');
   return original;
}

std::string getConstantStr(Constant& original)
{
    std::string rtStr = "";
    if(isa<ConstantFP>(original))
    {
        ConstantFP& fpRef = cast<ConstantFP>(original);
        APFloat pf = fpRef.getValueAPF();
        SmallVector<char, 32> Buffer;
        pf.toString(Buffer, 10,10);

        for(SmallVector<char, 32>::iterator cur=Buffer.begin(), end=Buffer.end();cur!=end; cur++ )
            rtStr.append(1,*cur);


    }
    else if(isa<ConstantInt>(original))
    {
        ConstantInt& intRef = cast<ConstantInt>(original);
        APInt pint = intRef.getValue();
        std::string str=pint.toString(10,true);
        rtStr = rtStr +str;

    }
    else
    {
        errs()<<"unsupported constant\n";
        exit(1);
    }

    return rtStr;
}

#endif
