#ifndef GENERATEHLSENV_H
#define GENERATEHLSENV_H

#include "llvm/Support/IncludeFile.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/Constants.h"
#include "llvm/Pass.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/raw_ostream.h"
#include "InstructionGraph.h"
#include "generatePartitionsUtil.h"
#include "generateCInstruction.h"
#include <string>
#include <stdio.h>
#include <ctype.h>

static void addBarSubTabs(bool addBarSub);
static bool genCPUCode();
static void addTabbedLine(std::string& original, std::string next);


std::string genIncludeQuote(std::string fileName)
{
    return "#include "+"\""+fileName+"\"";
}

static std::string genNormalInclude(std::string functionName, int numStages)
{
    // a few standard include
    std::string allInclude ="";
    addTabbedLine(allInclude, "#include <stdio.h>");
    addTabbedLine(allInclude, genIncludeQuote("platform.h"));
    addTabbedLine(allInclude, genIncludeQuote("xparameters.h"));
    addTabbedLine(allInclude, genIncludeQuote("xil_printf.h"));
    addTabbedLine(allInclude, genIncludeQuote("xscugic.h"));
    addTabbedLine(allInclude, genIncludeQuote("xdmaps.h"));
    addTabbedLine(allInclude, genIncludeQuote("scutimer.h"));
    for(unsigned int ind = 0; ind < numStages; ind++)
    {
        addTabbedLine(allInclude,genIncludeQuote("x"+functionName+int2Str(ind)+".h"));
    }
    return allInclude;

}
static std::string genNormalDef()
{
    return "#define TIMER_LOAD_VALUE 0xFFFFFFFF\n"+"#define TIMER_DEVICE_ID XPAR_SCUTIMER_DEVICE_ID\n";
}

void toUpperString(std::string& original)
{
    for(unsigned int charInd = 0; charInd < original.size(); charInd++)
    {
       x = toupper(x);
    }
}

static std::string genStageSpecificDec(std::string functionName, int stageInd, std::vector<argPair*>& funcArg)
{
    std::string stageName = functionName+int2Str(stageInd);

    std::string curStageName = "X"+(char)(toupper(stageName.at(0)))+stageName.substr(1);
    std::string curStageInstance = stageName+"_dev";
    // stage dec
    std::string stageDec = curStageName+" "+curStageInstance+"\n";

    // stage config dec
    std::string curStageConfigName = curStageInstance+"config";
    std::string curStageConfigStr = curStageName+"_Config";
    curStageConfigStr+=" "+curStageConfigName+" = {";
    addBarSubTabs(true);
    std::string dupStageName = stageName;
    toUpperString(dupStageName);
    addTabbedLine(curStageConfigStr, "0,"+toUpperString("XPAR_"+dupStageName+"_S_AXI_CB_BASEADDR"));
    addBarSubTabs(false);
    addTabbedLine(curStageConfigStr,"}" );

    // stage init
    std::string stageSetup = "void setup"+stageName;
    addTabbedLine(stageSetup,"{");
    addBarSubTabs(true);
    addTabbedLine(stageSetup,"int status = "+curStageName+"_Initialize(&"+curStageInstance+",&"+curStageConfigName+");\n");
    addTabbedLine(stageSetup,"if(status!=XST_SUCCESS) xil_printf(\"cannot initialize "+ stageName +"\\n\\r\");");
    addBarSubTabs(false);
    addTabbedLine(stageSetup,"}");

    // write stuff to stage
    std::string stageWriteFunc = "write2Setting_"+curStageInstance;
    std::string stageWrite = "int "+stageWriteFunc+"(u32 data)";
    addTabbedLine(stageWrite,"{");
    addBarSubTabs(true);
    addTabbedLine(stageWrite,curStageName+"_SetSettings(&"+curStageInstance+",data);");
    addTabbedLine(stageWrite,curStageName+"_SetSettingsVld(&"+curStageInstance+");");
    addTabbedLine(stageWrite,"data = 1;");
    addTabbedLine(stageWrite,"int m = 0;");
    addTabbedLine(stageWrite,"while(data!=0&&m<100)");
    addTabbedLine(stageWrite,"{");
    addBarSubTabs(true);
    addTabbedLine(stageWrite,"data = "+curStageName+"_GetSettingsVld(&"+curStageInstance+");");
    addTabbedLine(stageWrite,"m++;");
    addBarSubTabs(false);
    addTabbedLine(stageWrite,"}");
    addTabbedLine(stageWrite,"return data;");
    addBarSubTabs(false);
    addTabbedLine("}");

    // here we run it, we need to pass a the function argument to it
    std::string stageRun = "int run_"+curStageInstance+"(";
    for(unsigned int argInd = 0; argInd <funcArg.size(); argInd++)
    {
        argPair* curArg = funcArg.at(argInd);
        stageRun+=curArg->argType+" "+curArg->argName;
        if(argInd!=funcArg.size())
            stageRun+=",";

    }
    stageRun+=")";
    addTabbedLine(stageRun,"{");
    addBarSubTabs(true);
    addTabbedLine(stageRun,"int mCount;");
    addTabbedLine(stageRun, curStageName+"_Start(&"+curStageInstance+");");
    for(unsigned int argInd = 0; argInd < funcArg.size(); argInd++)
    {
        argPair* curArg = funcArg.at(argInd);
        addTabbedLine(stageRun, "mCount = "+stageWriteFunc+"((u32)"+curArg->argName+");");
        addTabbedLine(stageRun, "if(mCount == 1)");
        addTabbedLine(stageRun,"{");
        addBarSubTabs(true);
        addTabbedLine(stageRun,"xil_printf(\"cannot write "+curArg->argName+"\\n\\r\");");
        addTabbedLine(stageRun,"return 1;");
        addBarSubTabs(false);
        addTabbedLine(stageRun,"}");

    }
    addTabbedLine(stageRun,"return 0;");
    addBarSubTabs(false);
    addTabbedLine(stageRun,"}");

    // now define checking if things are done
    // and get return value if necessary

    return stageDec+curStageConfigStr;
}

#endif // GENERATEHLSENV_H
