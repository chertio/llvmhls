#ifndef GENERATECFUNCTIONS_H
#define GENERATECFUNCTIONS_H
#include "generatePartitions.h"
#include "generatePartitionsUtil.h"
#include "generateCInstruction.h"
static int numTabs =0;

struct argPair
{
    Type* argType;
    std::string argName;
    // 0 means read, 1 means write, 2 means read/write
    char dir;
};

struct InstructionGenerator
{
    Instruction* insn;
    int seqNum;
    bool remoteSrc;
    bool remoteDst;
    void init(Instruction* curIns,int n, bool rs, bool rd)
    {
        insn = curIns;
        seqNum = n;
        remoteSrc = rs;
        remoteDst = rd;
    }
    void generateStatement(std::vector<std::string>& partitionDecStr,
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
    }

};

// for the following lines,add/reduce tabs
static void alterTabs(bool addBarSub)
{
    if(addBarSub)
        numTabs++;
    else
        numTabs--;
}
static std::string addTabbedLine(std::string original, std::string next)
{
    std::string rtStr=original+"\n";
    for(unsigned tabCount = 0; tabCount<numTabs; tabCount++)
    {
        rtStr += "\t";
    }
    return rtStr+next;
}


static std::string generateSingleStatement(Instruction* curIns, bool remoteSrc, bool remoteDst,
                                           int seqNum,std::vector<std::string>& partitionDecStr,
                                           std::vector<argPair*>& functionArgs, std::vector<argPair*>& fifoArgs, BBMap2outStr* phiPreAssign =0
                                            )
{
    // first we ll see if the output value is defined already

    // if this is a terminator the the def will be the brTag
    // the Q has name "'brTag'Q", the actual tag has name 'brTag'
    // brTag name is formed by concat the srcBB of branch and the dstBBs
    // it is gonna be a read, then a switch -- with multiple dest

    // sometimes a varDec is not needed, if this is a terminator, and
    // this is actual...note we are pushing the seq number of successors
    // and they are not named

    std::string varDecStr = generateVariableStr(curIns,seqNum);
    if(curIns->isTerminator() && !remoteSrc   )
    {
        // do nothing when this is the terminator and then it is generated locally
    }
    else
    {
        partitionDecStr.push_back(varDecStr);
    }
    //std::string varName = generateVariableName(curIns,seqNum);

    std::string rtStr;
    //special case when it is a remote control flow change
    //read locally
    if(curIns->isTerminator()&&!isa<ReturnInst>(*curIns))
    {
        // as a terminator, we should check if this dude has
        // any successor
        unsigned numSuc = cast<TerminatorInst>(*curIns).getNumSuccessors();
        assert(numSuc < 255);
        if(remoteSrc)
        {
            // apparently we will need a remote src -- we need an argument

            rtStr = generateGettingRemoteBranchTag(cast<TerminatorInst>(*curIns),seqNum, fifoArgs);
            //errs()<<rtStr;

        }
        else
        {
            // we generate the local non return terminator
            // and possibly write the tag into the channel
            rtStr = generateControlFlow(cast<TerminatorInst>(*curIns),remoteDst,seqNum, fifoArgs, functionArgs);

            //errs()<<rtStr;


        }
        // we dont need the the value
        //return generateTerminatorStr(curIns);
    }
    // if this is return, it should be pretty easy.
    else if(isa<ReturnInst>(*curIns))
    {
        // return can never have remote src
        // the ins generating the return value
        // has remote src -- note only srcIns can have remote src, and the data
        // obtained from the channel get used by other
        // instruction in the local partition
        // returnInst doesnt have anything to be used by other instruction
        // it is possible it has functional argument as argument
        rtStr = rtStr+ generateReturn(cast<ReturnInst>(*curIns), functionArgs);
    }
    else if(curIns->isBinaryOp())
    {
        if(remoteSrc)
            rtStr =generateGettingRemoteData(*curIns,seqNum,fifoArgs);
        else
        {
            // this may have stuff from the function arg, also may write to fifo args
            rtStr =generateBinaryOperations(cast<BinaryOperator>(*curIns), remoteDst, seqNum, fifoArgs, functionArgs);
        }
    }
    else if(curIns->getOpcode()<Instruction::MemoryOpsEnd &&curIns->getOpcode() >= Instruction::MemoryOpsBegin  )
    {
        if(remoteSrc)
            rtStr = generateGettingRemoteData(*curIns,seqNum,fifoArgs);
        else
            rtStr = generateMemoryOperations(*curIns,remoteDst, seqNum,fifoArgs, functionArgs);
    }
    else if(curIns->getOpcode()<Instruction::CastOpsEnd && curIns->getOpcode()>= Instruction::CastOpsBegin)
    {
        if(remoteSrc)
            rtStr = generateGettingRemoteData(*curIns,seqNum,fifoArgs);
        else
            rtStr = generateCastOperations(*curIns, remoteDst, seqNum,fifoArgs,functionArgs);
    }
    // other operators --- we only deal with Phi and Select
    // how do we do phi?
    // we need to find all the predecessors of the current basic block
    else if(curIns->getOpcode()==Instruction::PHI)
    {
        if(remoteSrc)
            rtStr = generateGettingRemoteData(*curIns,seqNum,fifoArgs);
        else
        {

            rtStr = generatePhiNode(cast<PHINode>(*curIns), remoteDst, seqNum, phiPreAssign,fifoArgs,functionArgs);
        }

    }
    else if(curIns->getOpcode()==Instruction::Select)
    {
        if(remoteSrc)
            rtStr = generateGettingRemoteData(*curIns,seqNum,fifoArgs);
        else
        {
            rtStr = generateSelectOperations(cast<SelectInst>(*curIns), remoteDst, seqNum,fifoArgs,functionArgs);
        }
    }
    else if(curIns->getOpcode()==Instruction::ICmp || curIns->getOpcode()==Instruction::FCmp)
    {

        // got to generate the cmpare statement
        if(remoteSrc)
            rtStr = generateGettingRemoteData(*curIns,seqNum,fifoArgs);
        else
        {
            rtStr = generateCmpOperations(cast<CmpInst>(*curIns), remoteDst, seqNum,fifoArgs,functionArgs);
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



static std::string generateCPUCode(PartitionGen* pg)
{
    std::string allPartition="";
    for(unsigned int partInd = 0; partInd < pg->partitions.size(); partInd++)
    {
        DAGPartition* curPart = partitions.at(partInd);
        allPartition+="/* Partition "+ int2Str(partInd)+"*/\n";
        allPartition+=generateCPUCodePerPartition(pg,curPart);
    }
}

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
    /*****this is the part where we make the argument*****/
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

    /*****end****/
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


#endif // GENERATECFUNCTIONS_H
