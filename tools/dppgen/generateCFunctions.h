#ifndef GENERATECFUNCTIONS_H
#define GENERATECFUNCTIONS_H
#include "generatePartitions.h"
#include "generatePartitionsUtil.h"
#include "generateCInstruction.h"

int fifoSize = 64;
static int numTabs =0;

static bool CPU_bar_HLS;
// for the following lines,add/reduce tabs
static void addBarSubTabs(bool addBarSub)
{
    if(addBarSub)
        numTabs++;
    else
        numTabs--;
}

static bool genCPUCode()
{
    return CPU_bar_HLS;
}

// for everyline in string next, we add appropriate number of tabs
static void addTabbedLine(std::string& original, std::string next)
{
    //original+="\n";
    // get every line
    std::stringstream multiLine(next);
    std::string curLine;

    while(std::getline(multiLine,curLine))
    {
        original+="\n";
        for(unsigned tabCount = 0; tabCount<numTabs; tabCount++)
        {
            original += "\t";
        }
        original+=curLine;

    }
}


struct FunctionGenerator
{
    PartitionGen* pg;
    DAGPartition* myPartition;

    BBMap2Ins* srcBBs;
    BBMap2Ins* insBBs;
    std::vector<BasicBlock*>* BBList;



    std::vector<std::string> partitionDecStr;
    std::vector<argPair*> functionArgs;
    std::vector<argPair*> fifoArgs;
    BBMap2outStr phiPreAssign;
    std::vector<std::vector<std::string>*> BBActualStr;

    int partGenId;

    bool encloseWhileLoop;
    void init(PartitionGen* p, DAGPartition* pa, int partInd);
    void checkBBListValidityRearrangeDom();
    std::string genFunctionDeclaration();
    void generateFlowOnlyBlock(BasicBlock* curBB, std::vector<std::string>* curBBStrArray);
    void generateContentBlock(BasicBlock* curBB,std::vector<std::string>* curBBStrArray);
    std::string genVarDecl();
    std::string genBBsContent(std::string endgroup);
    std::string genFunctionBody(std::string endgroup);
    void generateCode();
};

struct InstructionGenerator
{
    Instruction* insn;
    int seqNum;
    bool remoteSrc;
    bool remoteDst;
    FunctionGenerator* owner;
    void init(Instruction* curIns,int n, bool rs, bool rd, FunctionGenerator* fg)
    {
        insn = curIns;
        seqNum = n;
        remoteSrc = rs;
        remoteDst = rd;
        owner = fg;
    }



    // memory dependency? to enforce this, we need a way to make sure the completion of outstanding
    // memory transactions before initiation of another group of memory transaction---not here
    // should be at the top level ip integrator, note, the initiation of the memory transaction
    // would have already been ordered properly
    std::string generateStatement()
    {
        std::string varDecStr = generateVariableDeclStr(insn,seqNum);
        //unless it is terminator&locally generated, we need to declare
        // a variable
        if(!(insn->isTerminator() && !remoteSrc))
        {
            owner->partitionDecStr.push_back(varDecStr);
        }
        // now got to generate the real thing
        std::string rtStr;
        //special case when it is a remote control flow change
        //read locally
        if(insn->isTerminator()&&!isa<ReturnInst>(*insn))
        {
            // as a terminator, we should check if this dude has
            // any successor
            unsigned int numSuc = cast<TerminatorInst>(*insn).getNumSuccessors();
            assert(numSuc < 255);
            if(remoteSrc)
            {
                // apparently we will need a remote src -- we need an argument

                rtStr = generateGettingRemoteBranchTag(cast<TerminatorInst>(*insn),seqNum, owner->fifoArgs);
                //errs()<<rtStr;

            }
            else
            {
                // we generate the local non return terminator
                // and possibly write the tag into the channel
                rtStr = generateControlFlow(cast<TerminatorInst>(*insn),remoteDst,seqNum, owner->fifoArgs, owner->functionArgs);




            }
        }
        // if this is return, it should be pretty easy.
        else if(isa<ReturnInst>(*insn))
        {
            // return can never have remote src
            // the ins generating the return value
            // has remote src -- note only srcIns can have remote src, and the data
            // obtained from the channel get used by other
            // instruction in the local partition
            // returnInst doesnt have anything to be used by other instruction
            // it is possible it has functional argument as argument
            rtStr =  generateReturn(cast<ReturnInst>(*insn), owner->functionArgs);
        }
        else if(insn->isBinaryOp())
        {
            if(remoteSrc)
                rtStr =generateGettingRemoteData(*insn,seqNum,owner->fifoArgs);
            else
            {
                // this may have stuff from the function arg, also may write to fifo args
                rtStr =generateBinaryOperations(cast<BinaryOperator>(*insn), remoteDst, seqNum, owner->fifoArgs, owner->functionArgs);
            }
        }
        else if(insn->getOpcode()<Instruction::MemoryOpsEnd &&insn->getOpcode() >= Instruction::MemoryOpsBegin  )
        {
            if(remoteSrc)
                rtStr = generateGettingRemoteData(*insn,seqNum,owner->fifoArgs);
            else
                rtStr = generateMemoryOperations(*insn,remoteDst, seqNum,owner->fifoArgs, owner->functionArgs);
        }
        else if(insn->getOpcode()<Instruction::CastOpsEnd && insn->getOpcode()>= Instruction::CastOpsBegin)
        {
            if(remoteSrc)
                rtStr = generateGettingRemoteData(*insn,seqNum,owner->fifoArgs);
            else
                rtStr = generateCastOperations(*insn, remoteDst, seqNum,owner->fifoArgs,owner->functionArgs);
        }
        // other operators --- we only deal with Phi and Select
        // how do we do phi?
        // we need to find all the predecessors of the current basic block
        else if(insn->getOpcode()==Instruction::PHI)
        {
            if(remoteSrc)
                rtStr = generateGettingRemoteData(*insn,seqNum,owner->fifoArgs);
            else
            {

                rtStr = generatePhiNode(cast<PHINode>(*insn), remoteDst, seqNum, owner->phiPreAssign,owner->fifoArgs,owner->functionArgs);
            }

        }
        else if(insn->getOpcode()==Instruction::Select)
        {
            if(remoteSrc)
                rtStr = generateGettingRemoteData(*insn,seqNum,owner->fifoArgs);
            else
            {
                rtStr = generateSelectOperations(cast<SelectInst>(*insn), remoteDst, seqNum,owner->fifoArgs,owner->functionArgs);
            }
        }
        else if(insn->getOpcode()==Instruction::ICmp || insn->getOpcode()==Instruction::FCmp)
        {

            // got to generate the cmpare statement
            if(remoteSrc)
                rtStr = generateGettingRemoteData(*insn,seqNum,owner->fifoArgs);
            else
            {
                rtStr = generateCmpOperations(cast<CmpInst>(*insn), remoteDst, seqNum,owner->fifoArgs,owner->functionArgs);
            }
        }
        else
        {
            errs()<<" problem unhandled instruction in generate single statement";
            exit(1);
        }

        // if this is
        //errs()<<(*curIns)<<"\n";
        // if it is remote src
        return rtStr;

    }

    /*void generateStatement(std::vector<std::string>& partitionDecStr,
                           std::vector<argPair*>& functionArgs,
                           std::vector<argPair*>& fifoArgs,
                           BBMap2outStr* phiPreAssign =0)
    {
        std::string varDecStr = generateVariableStr(curIns,seqNum);
        // if it is terminator and remotely generated,we need the decalaration
        if(!(curIns->isTerminator() && !remoteSrc))
        {
            partitionDecStr.push_back(varDecStr);
        }
    }*/

};

void FunctionGenerator::init(PartitionGen* p, DAGPartition* pa,  int partInd)
{
    pg = p;
    srcBBs = pg->srcBBsInPartition[pa];
    insBBs = pg->insBBsInPartition[pa];
    BBList = pg->allBBsInPartition[pa];

    myPartition = pa;
    partGenId = partInd;
}
// we also decide if while should be inserted
void FunctionGenerator::checkBBListValidityRearrangeDom()
{
    // now find the dominator for this list of BB
    BasicBlock* domBB = BBList->at(0);
    DominatorTree* dt = pg->getAnalysisIfAvailable<DominatorTree>();
    for(unsigned int bbInd = 1; bbInd < BBList->size(); bbInd++)
    {
        domBB = dt->findNearestCommonDominator(domBB,BBList->at(bbInd));
    }
    // the dominator must be inside the list
    std::vector<BasicBlock*>::iterator domIter = std::find(BBList->begin(),BBList->end(),domBB);
    // also if the encloseWhileLoop is false --> we are duplicating control flow
    // then the actual dominator must be the first when generating the final code
    // we should search for it and change the place

    assert(domIter!=BBList->end());
    BBList->erase(domIter);
    BBList->insert(BBList->begin(),domBB);
    // if we dont say no duplicate --> meaning we duplicate, then the purpose is to
    // have no while(1) --> which means any non-included BBs we branch to, must be
    // outside of anyloop, such that there is no path of coming back once we exit
    LoopInfo* li = pg->getAnalysisIfAvailable<LoopInfo>();

    encloseWhileLoop=false;
    if(!(pg->NoCfDup))
    {
        for(unsigned int bbInd = 1; bbInd < BBList->size(); bbInd++)
        {
            BasicBlock* curBB = BBList->at(bbInd);
            TerminatorInst* curTerm = curBB->getTerminator();
            for(unsigned sucInd = 0; sucInd < curTerm->getNumSuccessors(); sucInd++)
            {
                BasicBlock* curSuc = curTerm->getSuccessor(sucInd);
                if(std::find(BBList->begin(),BBList->end(),curSuc) == BBList->end())
                {
                    assert(li->getLoopDepth(curSuc)==0);
                }
            }
        }
    }
    else
    {
        if(li->getLoopDepth(domBB)!=0)
            encloseWhileLoop=true;
    }


}
// the only reason this bb exist is because it is part of the
// control flow, no instruction(src or actual) got assigned to
// this block
void FunctionGenerator::generateFlowOnlyBlock(BasicBlock* curBB, std::vector<std::string>* curBBStrArray)
{
    Instruction* curTerm = curBB->getTerminator();
    // shouldnt be return coz the return block isnt in a path
    assert(!isa<ReturnInst>(*curTerm));
    int seqNum = curTerm->getParent()->getInstList().size()-1;
    addBarSubTabs(true);
    struct InstructionGenerator ig;
    ig.init(curTerm,seqNum,true,false,this);
    std::string termStr = ig.generateStatement();
    addBarSubTabs(false);
    //std::string termStr = generateSingleStatement(curTerm,true,false,seqNum,partitionDecStr,functionArgs, fifoArgs);
    curBBStrArray->push_back(termStr);

}
void FunctionGenerator::generateContentBlock(BasicBlock* curBB,std::vector<std::string>* curBBStrArray)
{
    std::vector<Instruction*>* srcIns = 0;
    std::vector<Instruction*>* actualIns = 0;

    if(srcBBs->find(curBB)!=srcBBs->end())
        srcIns = (*srcBBs)[curBB];

    if(insBBs->find(curBB)!=insBBs->end())
        actualIns = (*insBBs)[curBB];
    int instructionSeq = -1;
    addBarSubTabs(true);
    for(BasicBlock::iterator insPt = curBB->begin(), insEnd = curBB->end(); insPt != insEnd; insPt++)
    {
        instructionSeq ++;
        // it is possible that this instruction is not in srcBB nor insBB
        // then this is not converted to c, but if this is the terminator
        // we need t read the branch tag unless its return
        if(srcIns!=0 && (std::find(srcIns->begin(),srcIns->end(), insPt)==srcIns->end()) &&
           actualIns!=0 && (std::find(actualIns->begin(),actualIns->end(),insPt)==actualIns->end())
         )
        {
            if(insPt->isTerminator() && !isa<ReturnInst>(*insPt) )
            {
                struct InstructionGenerator ig;
                ig.init(insPt,instructionSeq,true,false,this);
                std::string srcInsStr = ig.generateStatement();
                //std::string srcInsStr = generateSingleStatement(insPt,true,false,instructionSeq,partitionDecStr, functionArgs,fifoArgs);
                curBBStrArray->push_back(srcInsStr);
            }
        }

        // another case is one of srcIns & actualIns is zero, but the non zero one
        // does not contain this instruction....we still need to add the control flow
        // for this basic block
        std::vector<Instruction*>* relevantIns=0;
        if(srcIns!=0 && actualIns==0)
            relevantIns = srcIns;
        if(srcIns==0 && actualIns!=0)
            relevantIns = actualIns;
        if(relevantIns!=0)
        {
            if(std::find(relevantIns->begin(),relevantIns->end(), insPt)==relevantIns->end())
            {
                if(insPt->isTerminator() && !isa<ReturnInst>(*insPt) )
                {
                    struct InstructionGenerator ig;
                    ig.init(insPt,instructionSeq,true,false,this);
                    curBBStrArray->push_back(ig.generateStatement());
                }
            }
        }

        // this instruction is in the srcBB, meaning its output is used by this partition
        // meaning the we should insert a blocking read from FIFO -- unless its in the actual
        // ins also
        if(srcIns!=0 && !(std::find(srcIns->begin(),srcIns->end(), insPt)==srcIns->end()))
        {
            if(actualIns==0 || (actualIns!=0 && (std::find(actualIns->begin(),actualIns->end(),insPt)==actualIns->end())))
            {
                struct InstructionGenerator ig;
                ig.init(insPt,instructionSeq,true,false,this);
                curBBStrArray->push_back(ig.generateStatement());
            }
        }

        // this instruction is the actual
        if(actualIns!=0 && !(std::find(actualIns->begin(),actualIns->end(),insPt)==actualIns->end()))
        {

            // this instruction is the actual, let's see if this ins is used by
            // instruction in other partition --
            // check all its user to see if it is being used by others
            // if it is then we should also add an entry in the channel list
            // also if this is an terminator, it may not have any use, but we may
            // still send brTag

            bool thereIsPartitionReceiving = false;
            std::string channelStr;
            // special case for terminator
            if(insPt->isTerminator()&& !isa<ReturnInst>(*insPt))
            {
                // are there other partitions having the same basicblock
                // we will need to pass the branch tag over as long as it is
                // the case
                for(unsigned sid = 0; sid < pg->partitions.size(); sid++)
                {
                    DAGPartition* destPart = pg->partitions.at(sid);
                    if(myPartition == destPart)
                        continue;
                    std::vector<BasicBlock*>* destPartBBs = pg->allBBsInPartition[destPart];

                    if(std::find(destPartBBs->begin(),destPartBBs->end(),curBB)!=destPartBBs->end())
                    {
                        // add the branchtage channel
                        pg->addChannelAndDepPartition(thereIsPartitionReceiving,insPt,channelStr,destPart,0,instructionSeq);
                    }
                }
            }
            else
            {
                for(Value::use_iterator curUser = insPt->use_begin(), endUser = insPt->use_end(); curUser != endUser; ++curUser )
                {
                    // now we look at each use, these instruction belows to some DAGNode which belongs to some
                    // DAGPartition
                    assert(isa<Instruction>(*curUser));
                    DAGPartition* curUsePart = pg->getPartitionFromIns(cast<Instruction>(*curUser));

                    if(curUsePart == myPartition)
                        continue;
                    pg->addChannelAndDepPartition(thereIsPartitionReceiving,insPt,channelStr,curUsePart,1,instructionSeq);

                }
            }
            InstructionGenerator ig;
            ig.init(insPt,instructionSeq,false,thereIsPartitionReceiving,this);
            curBBStrArray->push_back(ig.generateStatement());
        }
    }
    addBarSubTabs(false);
}
static std::string genFunctionDeclarationStr(std::string funcName, std::vector<argPair*>& allArgPair, Type* rInsnType)
{

    std::string rtType ="void";
    if(rInsnType)
    {


        rtType = getLLVMTypeStr(rInsnType);

    }
    std::string funDecl = rtType+" "+funcName;
    addTabbedLine(funDecl,"(");
    addBarSubTabs(true);
    for(unsigned k=0; k<allArgPair.size();k++)
    {
        argPair* curP = allArgPair.at(k);
        // make sure there is no repeat
        std::string argDec = generateArgStr(curP);
        if(k!=allArgPair.size()-1)
                argDec+=",";
        addTabbedLine(funDecl,argDec);
    }
    addBarSubTabs(false);
    addTabbedLine(funDecl,")");

    return funDecl;
}

std::string FunctionGenerator::genFunctionDeclaration()
{
    std::string funName = pg->curFunc->getName();
    funName+=int2Str(partGenId);
    std::vector<argPair*> allArgPair;

    for(unsigned k=0; k<functionArgs.size();k++)
    {
        argPair* curP = functionArgs.at(k);
        // make sure there is no repeat
        /*bool added = false;
        for(unsigned ki=0; ki<k; ki++)
        {
            // check if we already seen it
            argPair* checkP = functionArgs.at(ki);
            if(checkP->argName.compare( curP->argName)==0)
            {
                added = true;
                break;
            }
        }
        if(!added)
        {*/
        allArgPair.push_back(curP);
        //}

    }

    for(unsigned k=0; k<fifoArgs.size(); k++)
    {
        argPair* curP = fifoArgs.at(k);
        allArgPair.push_back(curP);
    }
    Type* rtType=0;
    if(this->myPartition->rInsn)
    {
        Instruction* rt = this->myPartition->rInsn;
        assert(isa<ReturnInst>(*rt));
        ReturnInst* rtInst = &(cast<ReturnInst>(*rt));
        rtType = rtInst->getReturnValue()->getType();
    }
    std::string funDecl = genFunctionDeclarationStr(funName,allArgPair,rtType);


    return funDecl;
}
std::string FunctionGenerator::genVarDecl()
{
    std::string curDec="";
    for(unsigned int decInd = 0; decInd<partitionDecStr.size(); decInd++)
    {
        addTabbedLine(curDec, partitionDecStr.at(decInd));

    }
    return curDec;
}

std::string FunctionGenerator::genBBsContent(std::string endgroup)
{
    std::string contentStr="";
    if(encloseWhileLoop)
    {

        addTabbedLine(contentStr,"while(1){");
        addBarSubTabs(true);
    }
    for(unsigned int s=0; s < BBActualStr.size(); s++)
    {
        std::vector<std::string>* curBBStr = BBActualStr.at(s);
        BasicBlock* curBB = BBList->at(s);
        // now traverse it

        for(unsigned int k =0; k<curBBStr->size(); k++)
        {
            if(k==curBBStr->size()-1)
            {
                if(phiPreAssign.find(curBB)!=phiPreAssign.end())
                {
                    std::vector<std::string>* allPhiStr = phiPreAssign[curBB];
                    for(unsigned phiInd = 0; phiInd < allPhiStr->size(); phiInd++)
                    {
                        addTabbedLine(contentStr,  allPhiStr->at(phiInd));
                    }

                }
            }
            addTabbedLine(contentStr, curBBStr->at(k));
        }
    }

    addTabbedLine(contentStr, endgroup);


    if(encloseWhileLoop)
    {
        addBarSubTabs(false);
        addTabbedLine(contentStr,"}");

    }
    return contentStr;

}

std::string FunctionGenerator::genFunctionBody(std::string endgroup)
{
    std::string funcBody = "";
    addTabbedLine(funcBody, "{");
    addBarSubTabs(true);
    addTabbedLine(funcBody,genVarDecl());

    // now do the actual computation
    addTabbedLine(funcBody,genBBsContent(endgroup));


    addBarSubTabs(false);
    addTabbedLine(funcBody, "}");




    return funcBody;
}

void removeDuplicateName(std::vector<argPair*>& functionArgs)
{
   for(unsigned int argInd=0; argInd<functionArgs.size(); argInd++)
   {
       argPair* curP = functionArgs.at(argInd);
       for(unsigned ki=argInd+1; ki<functionArgs.size(); ki++)
       {
           // check if we already seen it
           argPair* checkP = functionArgs.at(ki);
           if(checkP->argName.compare( curP->argName)==0)
           {
               functionArgs.erase(functionArgs.begin()+ki);
               ki--;
           }
       }
   }
}

void FunctionGenerator::generateCode()
{
    checkBBListValidityRearrangeDom();
    for(unsigned int curBBInd = 0; curBBInd < BBList->size(); curBBInd++)
    {
        BasicBlock* curBB = BBList->at(curBBInd);
        std::vector<std::string>* curBBStrArray = new std::vector<std::string>();
        BBActualStr.push_back(curBBStrArray);
        std::string bbname =  curBB->getName();
        bbname+=":";
        //bbname.append(":\n");
        curBBStrArray->push_back(bbname);

        if(srcBBs->find(curBB)==srcBBs->end() && insBBs->find(curBB)==insBBs->end())
        {
            generateFlowOnlyBlock(curBB,curBBStrArray);
            continue;
        }


        generateContentBlock(curBB, curBBStrArray);
        // all the per bb stuff is done

    }
    std::string endgroup = generateEndBlock(BBList);
    // remove the duplicate in the functionArg
    removeDuplicateName(this->functionArgs);

    // FIXME: rewrite
    //generate function name
    std::string funcDecl = this->genFunctionDeclaration();
    std::string funcBody = this->genFunctionBody(endgroup);


    pg->Out<<funcDecl;
    pg->Out<<funcBody;




//        partGenId++;
    pg->Out<<"//=========================================================================\n";
    // we are not deleting these if we are
    // generating for cpu code
    // the functionArgs and fifoArgs vector
    if(!genCPUCode())
    {
        for(unsigned k =0; k< functionArgs.size(); k++)
        {
            delete functionArgs.at(k);
        }

        for(unsigned k =0; k<fifoArgs.size();k++)
        {
            delete fifoArgs.at(k);
        }
    }



}

static void release2DVectorArgPair(std::vector<std::vector<argPair*>*>& allArgs)
{
    for(unsigned int argInd = 0; argInd < allArgs.size(); argInd++)
    {
        std::vector<argPair*>* curArgVecPtr = allArgs[argInd];
        for(unsigned int i = 0; i < curArgVecPtr->size(); i++)
        {
            delete curArgVecPtr->at(i);
        }
        delete curArgVecPtr;
    }
}
static std::string generateNewAllocate(std::string ptrStr, std::string fifoName)
{
    std::string typeName = ptrStr;
    int starInd = typeName.find('*');
    assert(starInd!=std::string::npos);
    std::string bufferType = typeName.erase(starInd,1);
    std::string allocaStr = ptrStr+" "+fifoName+" = new "+bufferType+";";
    return allocaStr;
}
static std::string generateConsumerChannelInfoName(std::string fifoName,int seqNum)
{
    return fifoName+"_CCH_"+int2Str(seqNum);
}

static std::string generateInterFuncFifoDecl(std::map<std::string,int>& fifoArgName2UseTimes,
                                                std::map<std::string, std::string> fifoArgName2Type)
{
    // we want to have a struct for each channel
    assert(fifoArgName2UseTimes.size()==fifoArgName2Type.size());
    std::string rtStr="";
    for(std::map<std::string,int>::iterator fifoArgIter = fifoArgName2UseTimes.begin(), fifoArgEnd = fifoArgName2UseTimes.end();
        fifoArgIter!=fifoArgEnd; ++fifoArgIter)
    {

        std::string fifoName = fifoArgIter->first;
        std::string typeName = fifoArgName2Type[fifoName];
        int numberOfFifo = fifoArgName2UseTimes[fifoName]-1;
        // replace channel_info with fifo_channel
        // now we need to make the actual fifo for this channel_info
        std::string channelInfoTypeName = typeName;
        int ciInd = channelInfoTypeName.find("channel_info");
        std::string actualFifoType = channelInfoTypeName.replace(ciInd,12,"fifo_channel");
        std::string actualFifoName = fifoName+"_fifo";

        std::string allocateNewFifo = generateNewAllocate(actualFifoType, actualFifoName );
        std::string newFifoInit = actualFifoName+"->init("+int2Str(numberOfFifo)+");";

        std::string allocateNewProducerCInfo = generateNewAllocate(typeName, fifoName);
        std::string newProducerCInfoInit = fifoName+"->init("+actualFifoName+",-1);";
        rtStr+=allocateNewFifo;
        rtStr+="\n";
        rtStr+=newFifoInit;
        rtStr+="\n";
        rtStr+=allocateNewProducerCInfo;
        rtStr+="\n";
        rtStr+=newProducerCInfoInit;
        rtStr+="\n\n";

        // now do the declaration for all the consumer port
        // the naming scheme: fifoName+seqNum
        for(unsigned int consumerIntfInd = 0; consumerIntfInd < numberOfFifo; consumerIntfInd++)
        {
            std::string curConsumerIntfName = generateConsumerChannelInfoName(fifoName,consumerIntfInd);
            rtStr+=generateNewAllocate(typeName, curConsumerIntfName);
            rtStr+="\n";
            rtStr+=curConsumerIntfName+"->init("+actualFifoName+","+int2Str(consumerIntfInd)+");";
            rtStr+="\n";
        }
        rtStr+="\n\n";


    }

    return rtStr;
}
static std::string generatePackageDecl(int packInd)
{
    std::string packDecl = "struct argPack"+int2Str(packInd);
    return packDecl;
}
static std::string generatePackageInstance(std::string packName,int packInd)
{
    std::string packIns = packName + " argPackage"+int2Str(packInd);
    return packIns;
}

static std::string generateIndiStageArguPackageDec(std::vector<std::vector<argPair*>*>& allFunctionArgs,
                                                std::vector<std::vector<argPair*>*>&allFifoArgs,
                                                   std::string& initStr)
{
    std::string rtStr="";
    assert(allFunctionArgs.size()==allFifoArgs.size());
    // we need to keep track of the seqence number of channel_info
    // the number stored there is the number of times it has been seen
    std::map<std::string, int> channelInfo2NumConsumerSeen;


    unsigned int numOfPackage = allFunctionArgs.size();
    for(unsigned int packInd = 0; packInd < numOfPackage; packInd++)
    {
        std::string curPackInitStr="";
        std::vector<argPair*>* curFuncArg = allFunctionArgs.at(packInd);
        std::vector<argPair*>* curFifoArg = allFifoArgs.at(packInd);
        std::string packDec = generatePackageDecl(packInd);
        std::string packField="";
        addBarSubTabs(true);
        for(unsigned int funcInd = 0; funcInd<curFuncArg->size(); funcInd++ )
        {
            argPair* curArg = curFuncArg->at(funcInd);
            addTabbedLine(packField,curArg->argType+" "+curArg->argName+";");
            curPackInitStr += curArg->argName;
            if(funcInd!=curFuncArg->size()-1 || curFifoArg->size()!=0)
                curPackInitStr+=",";
        }
        for(unsigned int fifoInd = 0; fifoInd < curFifoArg->size();fifoInd++)
        {
            argPair* curArg = curFifoArg->at(fifoInd);
            addTabbedLine(packField,curArg->argType+" "+curArg->argName+";");
            std::string fieldInitName;
            if(curArg->dir==1) // write port, the name is the raw argName
                fieldInitName = curArg->argName;
            else
            {
                int seqNum = 0;
                if(channelInfo2NumConsumerSeen.find(curArg->argName)==channelInfo2NumConsumerSeen.end())
                {
                    channelInfo2NumConsumerSeen[curArg->argName] = 1;
                }
                else
                {
                    seqNum = channelInfo2NumConsumerSeen[curArg->argName];
                    channelInfo2NumConsumerSeen[curArg->argName] = seqNum+1;
                }
                fieldInitName = generateConsumerChannelInfoName(curArg->argName, seqNum);
            }

            curPackInitStr += fieldInitName;
            if(fifoInd != curFifoArg->size()-1)
                curPackInitStr+=",";
        }
        addBarSubTabs(false);

        rtStr+=packDec+"\n{"+packField+"\n};\n";
        initStr+= generatePackageInstance(packDec,packInd)+" ={ " +curPackInitStr+"};\n";
    }

    return rtStr;


}

static std::string generateReturnVarName(Function* func)
{
    std::string rtStr = func->getName();
    rtStr += "ReturnVal";
    return rtStr;
}


static std::string generateFuncCallWrapper(std::string rawFuncName,std::vector<std::vector<argPair*>*>& allFunctionArgs,
                                           std::vector<std::vector<argPair*>*>&allFifoArgs, PartitionGen* pg)
{
    assert(allFunctionArgs.size()==allFifoArgs.size());
    int numberOfFunc = allFunctionArgs.size();
    std::string rtStr="";
    for(unsigned int funcInd = 0; funcInd<numberOfFunc; funcInd++)
    {

        std::string localFuncName =rawFuncName+int2Str(funcInd);
        std::string localWrapperName = localFuncName+"Wrapper";
        addTabbedLine(rtStr, "void* "+localWrapperName+"(void* arg)");
        addTabbedLine(rtStr,"{");

        addBarSubTabs(true);
        // do whole bunch of assignment
        std::string packName = generatePackageDecl(funcInd);
        std::string cast2Name = "localArg_PACKPLACE";
        addTabbedLine(rtStr,packName+"* "+cast2Name+" = ("+packName+"*)arg;" );
        std::vector<argPair*>* curFuncArgs = allFunctionArgs.at(funcInd);
        std::vector<argPair*>* curFifoArgs = allFifoArgs.at(funcInd);
        std::vector<argPair*> allArgs;
        allArgs.insert(allArgs.end(),curFuncArgs->begin(),curFuncArgs->end());
        allArgs.insert(allArgs.end(),curFifoArgs->begin(),curFifoArgs->end());

        std::string funcArgStr = "";
        for(unsigned int argInd = 0; argInd < allArgs.size(); argInd++)
        {
            argPair* curArg = allArgs.at(argInd);
            std::string varName = curArg->argName;

            addTabbedLine(rtStr,curArg->argType+" "+varName+"="+cast2Name+"->"+varName+";");
            funcArgStr+= varName;
            if(argInd!=allArgs.size()-1)
                funcArgStr+=",";
        }

        // now really do the function call;
        DAGPartition* curPart = pg->partitions.at(funcInd);
        std::string assign2RetVal = "";
        if(curPart->rInsn && pg->curFunc->getReturnType()->getTypeID()!=Type::VoidTyID)
        {
            assign2RetVal="*"+generateReturnVarName(pg->curFunc)+"=";
        }
        addTabbedLine(rtStr,assign2RetVal+localFuncName+"("+ funcArgStr +");");
        addBarSubTabs(false);
        addTabbedLine(rtStr,"}");
    }
    return rtStr;
}

static std::string generateThreadSetup(int threadCount)
{
    std::string rtStr = "pthread_t threads["+int2Str(threadCount) +"];\n";
    rtStr+="pthread_attr_t attr;\n";
    rtStr+="pthread_attr_init(&attr);\n";
    rtStr+="pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_JOINABLE);\n";
    return rtStr;

}
static std::string generateThreadJoin(int threadCount)
{
    std::string rtStr="";
    rtStr+= "int i;\n";
    std::string loopWait = "for (i=0; i<"+int2Str(threadCount)+"; i++) pthread_join(threads[i], NULL);";
    rtStr+=loopWait;

    return rtStr;
}

static std::string generateIndividualThreadLaunch(int threadInd,std::string origFuncName)
{
    std::string rtStr="";
    rtStr+= "pthread_create(&threads["+int2Str(threadInd)+"], &attr, "+origFuncName+"Wrapper,"+ "&argPackage"+int2Str(threadInd)+");";
    return rtStr;
}
static std::string generateAllocateReturnSpace(Function* func)
{
    std::string varName = generateReturnVarName(func);
    std::string varType = getLLVMTypeStr(func->getReturnType());
    std::string rtStr = varName+" = ("+varType+"*)malloc(sizeof("+varType+"));\n";
    return rtStr;
}

static std::string generateCPUDriver(PartitionGen* pg, std::vector<std::vector<argPair*>*>& allFunctionArgs,
                              std::vector<std::vector<argPair*>*>&allFifoArgs)
{
    std::string funcName = pg->curFunc->getName();

    std::vector<argPair*> funcArgInDecl;

    Function::ArgumentListType &Args(pg->curFunc->getArgumentList());
    for (Function::ArgumentListType::const_iterator i = Args.begin(),
                                                    e = Args.end();
         i != e; ++i) {
        const Value* curArgVal = &(*i);

        argPair* curTopArg = createArg(curArgVal->getName(), generateVariableType(curArgVal), curArgVal->getType()->getScalarSizeInBits(),0);
        funcArgInDecl.push_back(curTopArg);
    }
    std::string driverDecl = genFunctionDeclarationStr(funcName,funcArgInDecl,pg->curFunc->getReturnType());

    // how do we generate the fifo space?
    // for every fifo arg, we know how many occurrence there are
    // among all functions, one would be the src, the others would
    // be consumer
    std::map<std::string,int> fifoArgName2UseTimes;
    std::map<std::string, std::string> fifoArgName2Type;
    for(unsigned int fifoVecInd = 0; fifoVecInd<allFifoArgs.size(); fifoVecInd++)
    {
        std::vector<argPair*>* curPartitionFifo = allFifoArgs[fifoVecInd];
        for(unsigned int fifoInd = 0; fifoInd<curPartitionFifo->size(); fifoInd++)
        {
            argPair* curArgPair = curPartitionFifo->at(fifoInd);
            if(fifoArgName2UseTimes.find(curArgPair->argName) == fifoArgName2UseTimes.end())
            {
                fifoArgName2UseTimes[curArgPair->argName] = 1;
                fifoArgName2Type[curArgPair->argName] = curArgPair->argType;
            }
            else
                fifoArgName2UseTimes[curArgPair->argName] += 1;
        }
    }
    std::string allocateReturnSpace = "";
    if(pg->curFunc->getReturnType()->getTypeID()!=Type::VoidTyID)
    {
        allocateReturnSpace = generateAllocateReturnSpace(pg->curFunc);
    }
    std::string cpuFifoSpaceStr = generateInterFuncFifoDecl(fifoArgName2UseTimes,fifoArgName2Type);
    //errs()<< cpuFifoSpaceStr<<"\n";
    // now we generate the calling of function
    // note we have to package the argument of the threads into a void*
    std::string indiStageArguPackageInsInit="";
    std::string indiStageArguPackageDec = generateIndiStageArguPackageDec(allFunctionArgs,allFifoArgs,indiStageArguPackageInsInit);
    errs()<< indiStageArguPackageDec<<"\n";
    errs()<< indiStageArguPackageInsInit<<"\n";
    std::string functionCallThreadWrappers = generateFuncCallWrapper(funcName,allFunctionArgs,allFifoArgs,pg);
    std::string rtStr="";

    addTabbedLine(rtStr,indiStageArguPackageDec);
    addTabbedLine(rtStr, functionCallThreadWrappers);
    // add the wrapper for each function: the function generated
    // here would be run in thread
    addTabbedLine(rtStr, driverDecl);
    addTabbedLine(rtStr,"{");
    addBarSubTabs(true);

    addTabbedLine(rtStr,cpuFifoSpaceStr);
    addTabbedLine(rtStr,allocateReturnSpace);
    addTabbedLine(rtStr,indiStageArguPackageInsInit);
    addTabbedLine(rtStr,generateThreadSetup(pg->partitions.size()));
    // now generate the launch of threads
    for(unsigned int threadInd = 0; threadInd < pg->partitions.size(); threadInd++)
    {
        addTabbedLine(rtStr, generateIndividualThreadLaunch(threadInd,funcName+int2Str(threadInd)));
    }
    addTabbedLine(rtStr, generateThreadJoin(pg->partitions.size()));
    if(pg->curFunc->getReturnType()->getTypeID()!=Type::VoidTyID)
    {
        addTabbedLine(rtStr,"return *"+generateReturnVarName(pg->curFunc)+";\n");
    }
    addBarSubTabs(false);
    addTabbedLine(rtStr,"}");

    return rtStr;


}

static void generateCode(PartitionGen* pg, bool _CPU_bar_HLS)
{
    std::vector<std::vector<argPair*>*> allFunctionArgs;
    std::vector<std::vector<argPair*>*> allFifoArgs;
    CPU_bar_HLS = _CPU_bar_HLS;

    if(genCPUCode())
    {
        pg->Out<<"#include \"comm.h\"\n";
        // also we need to allocate space for return value
        if(pg->curFunc->getReturnType()->getTypeID()!=Type::VoidTyID)
        {
            std::string returnTypeStr = getLLVMTypeStr(pg->curFunc->getReturnType());
            pg->Out<<returnTypeStr+"* "+ generateReturnVarName(pg->curFunc)+";\n";
        }

    }

    for(unsigned int partInd = 0; partInd < pg->partitions.size(); partInd++)
    {
        DAGPartition* curPart = pg->partitions.at(partInd);
        FunctionGenerator curPartFunc;
        curPartFunc.init(pg,curPart,partInd);
        curPartFunc.generateCode();

        std::vector<argPair*>* curPartFuncArg = new std::vector<argPair*>(curPartFunc.functionArgs);
        std::vector<argPair*>* curPartFifoArg = new std::vector<argPair*>(curPartFunc.fifoArgs);
        allFunctionArgs.push_back(curPartFuncArg);
        allFifoArgs.push_back(curPartFifoArg);
    }

    if(genCPUCode())
    {
        // generate top level function
        // we need to generate the top level function
        // with the right argument
        // then for each fifo, we make a very big buffer
        // then we execute the functions as separate threads
       // pg->Out<<  generateCPUDriver(pg, allFunctionArgs, allFifoArgs);


        pg->Out<< generateCPUDriver(pg, allFunctionArgs, allFifoArgs);

        // release at the end
        release2DVectorArgPair(allFunctionArgs);
        release2DVectorArgPair(allFifoArgs);

    }
}
/*
static std::string generateCPUCodePerPartition(PartitionGen* pg, DAGPartition* pa)
{
    BBMap2Ins* srcBBs = pg->srcBBsInPartition[pa];
    BBMap2Ins* insBBs = pg->insBBsInPartition[pa];
    std::vector<BasicBlock*>* BBList = pg->allBBsInPartition[pa];
    // now find the dominator for this list of BB
    BasicBlock* domBB = BBList->at(0);
    DominatorTree* dt = pg->getAnalysisIfAvailable<DominatorTree>();
    for(unsigned int bbInd = 1; bbInd < BBList->size(); bbInd++)
    {
        domBB = dt->findNearestCommonDominator(domBB,BBList->at(bbInd));
    }
    // the dominator must be inside the list
    assert(std::find(BBList->begin(),BBList->end(),domBB)!=BBList->end());
    // we can generate the definition string, and create a mapping of instruction to def string



    //BBMap2outStr bb2Str;
    // each vector of string's last string is the terminator,
    // when we finally output the strings, we need to check if there is any phi
    // node inserted assignment before the terminator
    std::vector<std::vector<std::string>*> curPartitionBBStr;
    // all declarations of the var used in the partition
    std::vector<std::string> partitionDecStr;

    BBMap2outStr phiPreAssign;

    // we need to figure out the argument, these includes
    // the argument from the function -- these can be given to every partition
    // they may not always use it;
    // then we have those FIFOs --- in and out FIFOs
    std::vector<argPair*> functionArgs;
    std::vector<argPair*> fifoArgs;

    // this is also the place where we generate the connection
    // description?
    for(unsigned int curBBInd = 0; curBBInd < BBList->size(); curBBInd++)
    {
        BasicBlock* curBB = BBList->at(curBBInd);
        std::vector<std::string>* curBBStrArray = new std::vector<std::string>();
        //bb2Str[curBB] = curBBStrArray;
        curPartitionBBStr.push_back(curBBStrArray);
        std::string bbname =  curBB->getName();
        bbname.append(":\n");
        curBBStrArray->push_back(bbname);

        if(srcBBs->find(curBB)==srcBBs->end() && insBBs->find(curBB)==insBBs->end())
        {
            // basicblock takes in a branch tag only -- definitely not sending stuff to remote
            Instruction* curTerm = curBB->getTerminator();
            // shouldnt be return coz the return block isnt in a path
            assert(!isa<ReturnInst>(*curTerm));
            int seqNum = curTerm->getParent()->getInstList().size()-1;
            std::string termStr = generateSingleStatement(curTerm,true,false,seqNum,partitionDecStr,functionArgs, fifoArgs);
            curBBStrArray->push_back(termStr);
            continue;
        }
        std::vector<Instruction*>* srcIns = 0;
        std::vector<Instruction*>* actualIns = 0;
        if(srcBBs->find(curBB)!=srcBBs->end())
            srcIns = (*srcBBs)[curBB];

        if(insBBs->find(curBB)!=insBBs->end())
            actualIns = (*insBBs)[curBB];

        // now this bb is either a srcBB or actualInsBB
        int instructionSeq = -1;
        for(BasicBlock::iterator insPt = curBB->begin(), insEnd = curBB->end(); insPt != insEnd; insPt++)
        {
            errs()<<instructionSeq <<cast<Instruction>(*insPt)<<"\n";
            instructionSeq ++;
            // it is possible that this instruction is not in srcBB nor insBB
            // then this is not converted to c, but if this is the terminator
            // we need t read the branch tag unless its return
            if(srcIns!=0 && (std::find(srcIns->begin(),srcIns->end(), insPt)==srcIns->end()) &&
               actualIns!=0 && (std::find(actualIns->begin(),actualIns->end(),insPt)==actualIns->end())
             )
            {
                errs()<<"nothing "<<cast<Instruction>(*insPt)<<"\n";

                if(insPt->isTerminator() && !isa<ReturnInst>(*insPt) )
                {
                    std::string srcInsStr = generateSingleStatement(insPt,true,false,instructionSeq,partitionDecStr, functionArgs,fifoArgs);
                    curBBStrArray->push_back(srcInsStr);
                }
            }

            // another case is one of srcIns & actualIns is zero, but the non zero one
            // does not contain this instruction....we still need to add the control flow
            // for this basic block
            if(srcIns!=0 && actualIns==0)
            {
                if(std::find(srcIns->begin(),srcIns->end(), insPt)==srcIns->end())
                {
                    if(insPt->isTerminator() && !isa<ReturnInst>(*insPt) )
                        curBBStrArray->push_back(generateSingleStatement(insPt,true,false,instructionSeq,partitionDecStr,functionArgs,fifoArgs));
                }
            }
            if(srcIns==0 && actualIns!=0)
            {
                if(std::find(actualIns->begin(),actualIns->end(),insPt)==actualIns->end())
                {
                    if(insPt->isTerminator() && !isa<ReturnInst>(*insPt) )
                        curBBStrArray->push_back(generateSingleStatement(insPt,true,false,instructionSeq,partitionDecStr,functionArgs,fifoArgs));
                }
            }

            if(srcIns!=0 && !(std::find(srcIns->begin(),srcIns->end(), insPt)==srcIns->end()))
            {
                //
                // this instruction is in the srcBB, meaning its output is used by this partition
                // meaning the we should insert a blocking read from FIFO -- unless its in the actual
                // ins also
                // its not in the actual ins
                if(actualIns==0 || (actualIns!=0 && (std::find(actualIns->begin(),actualIns->end(),insPt)==actualIns->end())))
                {
                    errs()<<"src   "<<cast<Instruction>(*insPt)<<"\n";
                    std::string srcInsStr = generateSingleStatement(insPt,true,false,instructionSeq,partitionDecStr,functionArgs,fifoArgs);
                    curBBStrArray->push_back(srcInsStr);
                }
            }
            if(actualIns!=0 && !(std::find(actualIns->begin(),actualIns->end(),insPt)==actualIns->end()))
            {
                errs()<<"actual   "<<cast<Instruction>(*insPt)<<"\n";

                // this instruction is the actual, let's see if this ins is used by
                // instruction in other partition --
                std::vector<DAGPartition*>* curInsOwners = getPartitionFromIns(insPt);
                DAGPartition* curInsPart = curInsOwners->at(0);
                //FIXME:seems redundant, should be deleted I think
                assert(curInsPart == pa);
                // now check all its user to see if it is being used by others
                // if it is then we should also add an entry in the channel list
                // also if this is an terminator, it may not have any use, but we may
                // still send brTag

                bool thereIsPartitionReceiving = false;
                std::string channelStr;
                if(insPt->isTerminator()&& !isa<ReturnInst>(*insPt))
                {

                    // are there other partitions having the same basicblock
                    for(unsigned sid = 0; sid < partitions.size(); sid++)
                    {
                        DAGPartition* destPart = partitions.at(sid);
                        if(curInsPart == destPart)
                            continue;
                        std::vector<BasicBlock*>* destPartBBs = allBBsInPartition[destPart];

                        if(std::find(destPartBBs->begin(),destPartBBs->end(),curBB)!=destPartBBs->end())
                        {
                            // add the branchtage channel
                            addChannelAndDepPartition(thereIsPartitionReceiving,insPt,channelStr,destPart,0,instructionSeq);

                        }
                    }
                }
                else
                {
                     errs()<<"begin add channel";

                    for(Value::use_iterator curUser = insPt->use_begin(), endUser = insPt->use_end(); curUser != endUser; ++curUser )
                    {
                        // now we look at each use, these instruction belows to some DAGNode which belongs to some
                        // DAGPartition
                        assert(isa<Instruction>(*curUser));

                        std::vector<DAGPartition*>* curUseOwners=getPartitionFromIns(cast<Instruction>(*curUser));
                        DAGPartition* curUsePart = curUseOwners->at(0);

                        if(curUsePart == curInsPart)
                            continue;
                         // add the data channel to the database
                        errs()<<"before adding channel\n";
                         addChannelAndDepPartition(thereIsPartitionReceiving,insPt,channelStr,curUsePart,1,instructionSeq);
                         errs()<<"after adding channel\n";
                    }
                }
                errs()<<"done add channel";
                std::string actualInsStr = generateSingleStatement(insPt,false,thereIsPartitionReceiving,instructionSeq,partitionDecStr,functionArgs,fifoArgs,&phiPreAssign);
                curBBStrArray->push_back(actualInsStr);
                errs()<<"done actual\n";
            }



        }
    }

    errs()<<"before endgroup\n";
    std::string endgroup = generateEndBlock(BBList);
    // the only guy who do not need to reside on the while 1 loop is the dude with the
    // terminator of the entry block
    errs()<<"after endgroup\n";
    // now we can output


//generate function name
    this->Out<<curFunc->getName()<<int2Str(partGenId);
    this->Out<<"(";
    for(unsigned k=0; k<functionArgs.size();k++)
    {
        argPair* curP = functionArgs.at(k);
        // make sure there is no repeat
        bool added = false;
        for(unsigned ki=0; ki<k; ki++)
        {
            // check if we already seen it
            argPair* checkP = functionArgs.at(ki);
            if(checkP->argName.compare( curP->argName)==0)
            {
                added = true;
                break;
            }
        }
        if(!added)
        {
            std::string argDec = generateArgStr(curP);
            if(k!=0)
                this->Out<<",\n";
            this->Out<<argDec;
        }
    }

    for(unsigned k=0; k<fifoArgs.size(); k++)
    {
        argPair* curP = fifoArgs.at(k);
        std::string argDec = generateArgStr(curP);
        if(k!=0)
            this->Out<<",\n";
        else if(functionArgs.size()!=0)
            this->Out<<",\n";
        this->Out<<argDec;
    }

    this->Out<<")\n{\n";



    for(unsigned decInd = 0; decInd<partitionDecStr.size(); decInd++)
    {
        std::string curDec = partitionDecStr.at(decInd);
        this->Out<<curDec<<"\n";
    }

    bool encloseWhileLoop = false;
    // we sure dont need to enclose if we have cf dup
    if(NoCfDup &&  li->getLoopDepth(domBB)!=0)
    {
        encloseWhileLoop = true;
    }
    if(encloseWhileLoop)
    {
        this->Out<<"while(1){\n";
    }
    for(unsigned int s=0; s < curPartitionBBStr.size(); s++)
    {
        std::vector<std::string>* curBBStr = curPartitionBBStr.at(s);
        BasicBlock* curBB = BBList->at(s);
        // now traverse it

        for(unsigned int k =0; k<curBBStr->size(); k++)
        {
            if(k==curBBStr->size()-1)
            {
                //FIXME: only when the last ins is terminator
                // when we do this phi assignment
                //need to do the phi thing
                if(phiPreAssign.find(curBB)!=phiPreAssign.end())
                {
                    std::vector<std::string>* allPhiStr = phiPreAssign[curBB];
                    for(unsigned phiInd = 0; phiInd < allPhiStr->size(); phiInd++)
                    {
                        errs()<<"              "<<allPhiStr->at(phiInd)<<"\n";
                        this->Out<<allPhiStr->at(phiInd)<<"\n";
                    }

                }
            }
            this->Out<<curBBStr->at(k);
        }
    }

    // now we output the endgroup
    this->Out<<endgroup;
    if(encloseWhileLoop)
    {
        this->Out<<"\n}\n";
    }
    this->Out<<"\n}\n";


    partGenId++;
    this->Out<<"//=========================================================================\n";
    // clear the functionArgs and fifoArgs vector
    for(unsigned k =0; k< functionArgs.size(); k++)
    {
        delete functionArgs.at(k);
    }
    for(unsigned k =0; k<fifoArgs.size();k++)
    {
        delete fifoArgs.at(k);
    }

}
*/

#endif // GENERATECFUNCTIONS_H
