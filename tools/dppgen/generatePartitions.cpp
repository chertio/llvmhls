//===- generatePartition.cpp - generate instruction partitions for DPP -------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file provides passes to generate partitions from dataflow
//
//===----------------------------------------------------------------------===//
#include <sstream>
#include "llvm/ADT/SCCIterator.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/raw_ostream.h"
#include "InstructionGraph.h"
#include "generatePartitionsUtil.h"
#include "llvm/Analysis/Dominators.h"
#include "llvm/Analysis/PostDominators.h"
#include <vector>
#include <string>
#include <queue>
#define LONGLATTHRESHOLD 5
using namespace llvm;

namespace {
    struct DAGNode4Partition;
    struct DAGPartition;
    struct PartitionGen;
    typedef std::map<const Instruction *, DAGNode4Partition *> DagNodeMapTy;
    typedef std::map<const DAGNode4Partition*, DAGPartition *> DagPartitionMapTy;
    // this is used for srcBB and insBB things
    typedef std::map<BasicBlock*, std::vector<Instruction*>*> BBMap2Ins;
    typedef std::map<DAGPartition*, BBMap2Ins*> partitionToBB2InsInfo;
    typedef std::map<DAGPartition*, std::vector<BasicBlock*>*> partitionToBBList;

    typedef std::map<BasicBlock*, std::vector<std::string>*> BBMap2outStr;

    typedef std::map<Instruction*, std::string> InsMap2Str;




    // this is to keep track of the channels
    // we map instruction to tagName -- a string denoting the name of the channel

    // we also map tagName to user Partition -- there can be multiple destination
    typedef std::map<std::string, std::vector<DAGPartition*>*> strMap2PartitionVector;

    typedef BBMap2Ins::iterator BBMapIter;
    static void addBBInsToMap(BBMap2Ins& map, Instruction* curIns)
    {
        BasicBlock* bbKey = curIns->getParent();
        BBMap2Ins::iterator I = map.find(bbKey);
        if(I== map.end())
        {
            std::vector<Instruction*>* curBBIns = new std::vector<Instruction*>();
            curBBIns->push_back(curIns);
            map[bbKey] = curBBIns;
        }
        else
        {
            std::vector<Instruction*>* curBBIns = map[bbKey];
            // now check if it is already included
            if(std::find(curBBIns->begin(),curBBIns->end(),curIns )== curBBIns->end())
            {
                curBBIns->push_back(curIns);
            }
        }
    }

    static std::string generateTerminatorStr(Instruction* ins)
    {
        std::string a = "f";
        // find value
        return a;
    }

    static std::string generateSingleStatement(Instruction* curIns, bool remoteSrc, bool remoteDst, InsMap2Str& ins2def)
    {
        // first we ll see if the output value is defined already

        // if this is a terminator the the def will be the brTag
        // the Q has name "'brTag'Q", the actual tag has name 'brTag'
        // brTag name is formed by concat the srcBB of branch and the dstBBs
        // it is gonna be a read, then a switch -- with multiple dest
        if(curIns->isTerminator())
        {
            if(remoteSrc)
            {
                // we need to get remote target tag

            }
            // we dont need the the value
            return generateTerminatorStr(curIns);
        }

        // if it is remote src
        std::string a = "f";
        return a;
    }


    static bool searchToBasicBlock(std::vector<BasicBlock*>& storage, BasicBlock* current, BasicBlock* target, BasicBlock* domInter =0 )
    {
        //errs()<<" search to bb starting "<<current->getName()<<" towards "<<target->getName()<<"\n";
        storage.push_back(current);

        if(current == target)
        {

            return true;
        }
        bool keepCurrent = false;
        for(unsigned int ind = 0; ind < current->getTerminator()->getNumSuccessors(); ind++)
        {
            BasicBlock* curSuc = current->getTerminator()->getSuccessor(ind);
            if(std::find(storage.begin(),storage.end(),curSuc) != storage.end())
            {
                //curSuc already in the array, try the next one
                continue;
            }
            // if this path goes through dominator then its disregarded
            if(curSuc == domInter)
                continue;
            bool found = searchToBasicBlock(storage, curSuc, target);
            if(found)
            {
                //storage.push_back(curSuc);
                keepCurrent = true;
            }
        }
        if(!keepCurrent)
            storage.pop_back();
        return keepCurrent;
    }
    static void mergeInto(std::vector<BasicBlock*>& small, std::vector<BasicBlock*>& big)
    {
        //errs()<<"into merge";
        for(unsigned int pathInd=0; pathInd < small.size(); pathInd++)
        {
            BasicBlock* curPathBB = small.at(pathInd);
            if(std::find(big.begin(),big.end(),curPathBB)==big.end())
            {
                big.push_back(curPathBB);
            }
        }
        //errs()<<" outo merge";
    }


    static void addPathBBsToBBMap(BBMap2Ins& sourceBBs, BasicBlock* dominator, std::vector<BasicBlock*>& AllBBs )
    {
        std::vector<BasicBlock*> curPathStorage;

        for(BBMapIter bmi = sourceBBs.begin(), bme = sourceBBs.end(); bmi!=bme; ++bmi)
        {


            BasicBlock* dest=bmi->first;
           // errs()<<"serach towards " << dest->getName()<<"\n";
            if(searchToBasicBlock(curPathStorage,dominator,dest))
            {
                // got to put everything on the the AllBBs
                mergeInto(curPathStorage,AllBBs);

            }
            curPathStorage.clear();

        }
    }
    static void searchToGroupAndAdd(BasicBlock* curBB, BasicBlock* dominator, BBMap2Ins& destBBs,
                                    std::vector<BasicBlock*>& curPathStorage,std::vector<BasicBlock*>& AllBBs)
    {
        for(BBMapIter bmi2 = destBBs.begin(), bme2 = destBBs.end(); bmi2!=bme2; ++bmi2)
        {
            BasicBlock* destBB = bmi2->first;
            if(searchToBasicBlock(curPathStorage,curBB,destBB,dominator))
            {
                // now put everything into the AllBBs vector
                mergeInto(curPathStorage,AllBBs);
            }
            curPathStorage.clear();

        }
    }

    struct DAGNode4Partition{
        std::vector<InstructionGraphNode*>* dagNodeContent;
        bool singleIns;
        int sccLat;
        bool hasMemory;
        bool covered;
        int seqNum;
        void init()
        {
            singleIns = false;
            sccLat = 0;
            hasMemory = false;
            covered = false;
            seqNum = -1;
        }
        void print()
        {
            for(unsigned int insI = 0; insI < dagNodeContent->size(); insI++)
            {
                Instruction* curIns = dagNodeContent->at(insI)->getInstruction();
                errs()<<"\t"<<*curIns<<"\n";
            }
        }

    };
    struct PartitionGen : public FunctionPass {
      static char ID;  // Pass identification, replacement for typeid

      partitionToBB2InsInfo srcBBsInPartition;
      partitionToBB2InsInfo insBBsInPartition;
      // each partition's bb list
      partitionToBBList allBBsInPartition;

      InsMap2Str ins2Channel;
      strMap2PartitionVector channelFanOutPartition;


      //std::vector<DAGNode4Partition*> allDAGNodes;


      std::vector<DAGPartition*> partitions;

      // from instruction to node
      DagNodeMapTy dagNodeMap;
      // from node to partition
      DagPartitionMapTy dagPartitionMap;
      //


      PartitionGen() : FunctionPass(ID) {}
      bool runOnFunction(Function& func);

      void generatePartition(std::vector<DAGNode4Partition*> *dag);

      void generateControlFlowPerPartition();
      void print(raw_ostream &O, const Module* = 0) const { }

      void DFSCluster(DAGNode4Partition* curNode, DAGPartition* curPartition);
      void BFSCluster(DAGNode4Partition* curNode);
      void BarrierCluster(std::vector<DAGNode4Partition*> *dag);
      bool DFSFindPartitionCycle(DAGPartition* nextHop);

      virtual void getAnalysisUsage(AnalysisUsage &AU) const {
        AU.addRequired<InstructionGraph>();
        AU.addRequiredTransitive<DominatorTree>();
        AU.addRequired<PostDominatorTree>();
        AU.setPreservesAll();
      }
      DAGPartition* getPartitionFromIns(Instruction* ins)
      {
          DAGNode4Partition* node = dagNodeMap[const_cast<Instruction*>(ins)];
          DAGPartition* part = dagPartitionMap[const_cast<DAGNode4Partition*>(node)];
          return part;
      }
      void generateCFromBBList(DAGPartition* pa);



    };
    struct DAGPartition{
        // a partition contains a set of dagNode
        std::vector<DAGNode4Partition*> partitionContent;

        // let's add the pointer to the maps

        bool containMemory;
        bool containLongLatCyc;

        bool cycleDetectCovered;
        //DagNodeMapTy* insToDagNode;
        //DagPartitionMapTy* dagNodeToPartition;
        PartitionGen* top;

        void init(PartitionGen* tt )
        {
            containMemory = false;
            containLongLatCyc = false;
            cycleDetectCovered = false;
            top = tt;
        }
        void print()
        {
            for(unsigned int nodeI = 0; nodeI < partitionContent.size(); nodeI++)
            {
                DAGNode4Partition* curNode = partitionContent.at(nodeI);
                curNode->print();
                errs()<<"\n";
            }
        }
        void addDagNode(DAGNode4Partition* dagNode,DagPartitionMapTy &nodeToPartitionMap )
        {
            dagNode->print();
            partitionContent.push_back(dagNode);
            dagNode->covered=true;
            containMemory |= dagNode->hasMemory;
            containLongLatCyc |= (dagNode->sccLat >= LONGLATTHRESHOLD);
            nodeToPartitionMap[dagNode] = this;
        }



        void generateBBList(DominatorTree* DT, PostDominatorTree* PDT)
        {
            BBMap2Ins* sourceBBs = new BBMap2Ins;
            BBMap2Ins* insBBs = new BBMap2Ins;

            std::vector<Instruction*> srcInstructions;
            for(unsigned int nodeInd = 0; nodeInd < partitionContent.size(); nodeInd++)
            {
                DAGNode4Partition* curNode = partitionContent.at(nodeInd);
                for(unsigned int insInd = 0; insInd< curNode->dagNodeContent->size(); insInd++)
                {
                    Instruction* curIns = curNode->dagNodeContent->at(insInd)->getInstruction();

                    addBBInsToMap(*insBBs,curIns);
                    unsigned int numOp = curIns->getNumOperands();
                    for(unsigned int opInd = 0; opInd < numOp; opInd++)
                    {
                        Value* curOp = curIns->getOperand(opInd);
                        if(isa<Instruction>(*curOp))
                        {
                            Instruction* srcIns = &(cast<Instruction>(*curOp));
                            srcInstructions.push_back(srcIns);
                            addBBInsToMap(*sourceBBs,srcIns);
                        }
                    }
                }
            }



            // now make the instructions



            // dominator for src and ins BBs
            // this will be the first basicblock we need to convert
            // then we shall see where each bb diverge?
            BasicBlock* dominator=0;
            BasicBlock* prevBB=0;
            BasicBlock* postDominator=0;
            BasicBlock* prevBBPost = 0;

            for(BBMapIter bmi = sourceBBs->begin(), bme = sourceBBs->end(); bmi!=bme; ++bmi)
            {
                BasicBlock* curBB=bmi->first;
                //errs()<<curBB->getName()<<"\n";
                // now print out the source

                if(prevBB!=0)
                {
                    dominator = DT->findNearestCommonDominator(prevBB, curBB);
                    //errs()<<"\n"<<dominator->getName()<<"is the com anc of "<<prevBB->getName()<<" and "<<curBB->getName()<<"\n";
                    prevBB = dominator;
                }
                else
                    prevBB = curBB;

                if(prevBBPost!=0)
                {
                    postDominator = PDT->findNearestCommonDominator(prevBBPost,curBB);
                    //errs()<<"\n"<<postDominator->getName()<<"is the post com dom of "<<prevBBPost->getName()<<" and "<<curBB->getName()<<"\n";
                    prevBBPost = postDominator;
                }
                else
                    prevBBPost = curBB;
            }


            for(BBMapIter bmi = insBBs->begin(), bme = insBBs->end(); bmi!=bme; ++bmi)
            {
                BasicBlock* curBB=bmi->first;
                //errs()<<curBB->getName()<<"\n";
                // now print out the source

                if(prevBB!=0)
                {
                    dominator = DT->findNearestCommonDominator(prevBB, curBB);
                    //errs()<<"\n"<<dominator->getName()<<"is the com anc of "<<prevBB->getName()<<" and "<<curBB->getName()<<"\n";
                    prevBB = dominator;
                }
                else
                    prevBB = curBB;

                if(prevBBPost!=0)
                {
                    postDominator = PDT->findNearestCommonDominator(prevBBPost,curBB);
                   // errs()<<"\n"<<postDominator->getName()<<"is the post com dom of "<<prevBBPost->getName()<<" and "<<curBB->getName()<<"\n";
                    prevBBPost = postDominator;
                }
                else
                    prevBBPost = curBB;
            }
//errs()<<"before adding map\n";
            // let's filter out those irrelevant
            // how do we do this,
            // start from each srcBBs, search backward until dominator,
            // everything in between is to needed, -- if they are not srcBB nor insBBs
            // their terminator output would be needed

            // then go from each srcBBs and insBBs forward, until post dominator,
            // everything in between is needed, is it?
            // in the case of two BBs, if one BB is never reaching another BB
            // without going through dominator, then when this BB exits, we can
            // just wait in the dominator, so the procedure should be use
            // each BB as starting point to search for all other BBs, if any BB
            // is found all path to that BB should be included? if none can be found
            // then getting out of this BB is same as getting out of our subgraph

            // so naturally if we have everything within one BB, we just need that BB
            std::vector<BasicBlock*>* AllBBs = new std::vector<BasicBlock*>();
            // some of these BBs wont be in the map, in which case, we just need the terminator
            AllBBs->push_back(dominator);

            addPathBBsToBBMap(*sourceBBs,dominator,*AllBBs);
            addPathBBsToBBMap(*insBBs,dominator,*AllBBs);
            // now  we do the n^2 check to see if anybody goes to anybody else?
//errs()<<"done adding map\n";
            for(BBMapIter bmi = sourceBBs->begin(), bme = sourceBBs->end(); bmi!=bme; ++bmi)
            {
                BasicBlock* curBB=bmi->first;
                std::vector<BasicBlock*> curPathStorage;

                searchToGroupAndAdd(curBB,dominator,*sourceBBs,curPathStorage,*AllBBs);
                // same thing for insBB
                searchToGroupAndAdd(curBB,dominator,*insBBs,curPathStorage,*AllBBs);

            }
            for(BBMapIter bmi = insBBs->begin(), bme = insBBs->end(); bmi!=bme; ++bmi)
            {
                BasicBlock* curBB=bmi->first;
                std::vector<BasicBlock*> curPathStorage;

                searchToGroupAndAdd(curBB,dominator,*sourceBBs,curPathStorage,*AllBBs);
                // same thing for insBB
                searchToGroupAndAdd(curBB,dominator,*insBBs,curPathStorage,*AllBBs);

            }

            // now all the basicblocks are added into the allBBs
            (top->srcBBsInPartition)[this]=sourceBBs;
            (top->insBBsInPartition)[this]=insBBs;
            (top->allBBsInPartition)[this]=AllBBs;







            errs()<<"dominator is "<<dominator->getName()<<" post dom is "<<postDominator->getName()<<"\n";

            // go to release memory here

        }




    };
    static bool needANewPartition(DAGPartition* curPartition, DAGNode4Partition* curNode)
    {
        if((curNode->hasMemory  &&  (curPartition->containLongLatCyc || curPartition->containMemory))||
           ((!curNode->singleIns  && curNode->sccLat >= LONGLATTHRESHOLD)&& (curPartition->containMemory)))
            return true;
        else
            return false;
    }
    static void findDependentNodes(DAGNode4Partition* curNode, DagNodeMapTy &nodeLookup, std::vector<DAGNode4Partition*> &depNodes)
    {
        // how do we do this?
        // iterate through the instructionGraphNodes in curNode, and then
        // for each of them, look at instruction, and then lookup the node
        // in the map
        for(unsigned int i=0; i< curNode->dagNodeContent->size(); i++)
        {
            InstructionGraphNode* curInsNode = curNode->dagNodeContent->at(i);

            for(InstructionGraphNode::iterator depIns = curInsNode->begin(), depInsE = curInsNode->end();
                depIns != depInsE; ++depIns)
            {
                Instruction* curDepIns = depIns->second->getInstruction();
                DAGNode4Partition* node2add = nodeLookup[curDepIns];
                depNodes.push_back(node2add);

            }
        }
    }



}

char PartitionGen::ID = 0;
static RegisterPass<PartitionGen>
Y("dpp-gen", "generate decoupled processing functions for each function CFG");


bool compareDagNode(DAGNode4Partition* first, DAGNode4Partition* second)
{
    return first->seqNum < second->seqNum;
}

void PartitionGen::BarrierCluster(std::vector<DAGNode4Partition*> *dag)
{
    DAGPartition* curPartition = new DAGPartition;
    curPartition->init(this);
    partitions.push_back(curPartition);

    for(unsigned int dagInd = 0; dagInd < dag->size(); dagInd++)
    {

        DAGNode4Partition* curDagNode = dag->at(dagInd);
        if(needANewPartition(curPartition,curDagNode))
        {
            curPartition = new DAGPartition;
            curPartition->init(this);
            partitions.push_back(curPartition);
        }
        curPartition->addDagNode(curDagNode,dagPartitionMap);
    }
}

void PartitionGen::BFSCluster(DAGNode4Partition* curNode)
{
    //if(needANewPartition(curPartition,curNode))
    //    return;
    //else

    // create a new partition and add the seed node
    DAGPartition* curPartition = new DAGPartition;
    curPartition->init(this);
    partitions.push_back(curPartition);

    std::queue<DAGNode4Partition*> storage;

    curPartition->addDagNode(curNode,  dagPartitionMap);
    storage.push(curNode);
    //curPartition->addDagNode(curNode,  dagPartitionMap);
    while(storage.size()!=0)
    {
        DAGNode4Partition* nodeCheck = storage.front();
        storage.pop();
        std::vector<DAGNode4Partition*> depNodes;
        findDependentNodes(nodeCheck, dagNodeMap,depNodes);
        std::sort(depNodes.begin(),depNodes.end(), compareDagNode);
        for(unsigned int j = 0; j<depNodes.size(); j++)
        {

            DAGNode4Partition* nextNode = depNodes.at(j);
            if(nextNode->covered==false)
            {
                if(needANewPartition(curPartition,nextNode))
                {
                    // we need to create a new partition
                    curPartition = new DAGPartition;
                    curPartition->init(this);
                    partitions.push_back(curPartition);
                }
                curPartition->addDagNode(nextNode,  dagPartitionMap);
                storage.push(nextNode);
            }
        }
    }

}

void PartitionGen::DFSCluster(DAGNode4Partition* curNode, DAGPartition* curPartition)
{

    if(needANewPartition(curPartition,curNode))
        return;
    else
        curPartition->addDagNode(curNode,  dagPartitionMap);

    // now we shall figure out the next hop
    std::vector<DAGNode4Partition*> depNodes;
    findDependentNodes(curNode, dagNodeMap,depNodes);
    std::sort(depNodes.begin(),depNodes.end(), compareDagNode);
    // should sort the vector according to the seqNum of the nodes
    for(unsigned int j = 0; j<depNodes.size(); j++)
    {
        DAGNode4Partition* nextNode = depNodes.at(j);
        if(nextNode->covered==false)
            DFSCluster(nextNode, curPartition);
    }
}


#define NEWPARTEVERYSEED
//#define USEBFSCLUSTER
//#define USEBFSCLUSTER
#define USEBARRIERCLUSTER
void PartitionGen::generatePartition(std::vector<DAGNode4Partition*> *dag)
{

#ifdef USEBARRIERCLUSTER
    BarrierCluster(dag);
#else

    for(unsigned int dagInd = 0; dagInd < dag->size(); dagInd++)
    {
        DAGNode4Partition* curNode = dag->at(dagInd);
        if(curNode->covered)
            continue;
#ifdef USEDFSCLUSTER
        DAGPartition* curPartition = 0;

#ifdef NEWPARTEVERYSEED
        curPartition = new DAGPartition;
        curPartition->init();
        partitions.push_back(curPartition);

#else
        if(!curPartition)
        {
            curPartition = new DAGPartition;
            curPartition->init();
            partitions.push_back(curPartition);
        }
        // if curnode has memory or it is long latency cycle
        else if(needANewPartition(curPartition,curNode))
        {
            // time to start a new partition
            curPartition = new DAGPartition;
            curPartition->init();
            partitions.push_back(curPartition);
        }
#endif
        // DFS has problem
        DFSCluster(curNode, curPartition);
#else
        BFSCluster(curNode);

#endif
    }
#endif


    /*errs()<<"#of partitions :"<<partitions.size()<<"\n";
    for(unsigned int ai = 0; ai<partitions.size(); ai++)
    {
        errs()<<"partitions :"<<ai <<partitions.at(ai)->partitionContent.size()<<"\n";
    }
    for(unsigned int ai = 0; ai<partitions.size(); ai++)
    {
        DAGPartition* curPar = partitions.at(ai);
        std::vector<DAGNode4Partition*>* nodeVector = &(curPar->partitionContent);
        errs()<<"partition"<< ai<<"\n";
        for(unsigned int nodeI = 0; nodeI <nodeVector->size(); nodeI++)
        {

            DAGNode4Partition* curNode = nodeVector->at(nodeI);
            for(unsigned int insI = 0; insI < curNode->dagNodeContent->size(); insI++)
            {
                Instruction* curIns = curNode->dagNodeContent->at(insI)->getInstruction();
                errs()<<"\t"<<*curIns<<"\n";
            }
            errs()<<"\n";
        }
    }*/
}



void PartitionGen::generateControlFlowPerPartition()
{
    // go through every partition, for each partition
    // go through all the instructions
    // for each instruction, find where their operands are from
    // then these are all the basic blocks we need ? dont we need more
    // control dependence communication -- lets not have it and check
    // for cyclic dependence

    // lets check if there is any cycle between the partitions

    for(unsigned int pi = 0; pi < partitions.size(); pi++)
    {
        errs()<<pi<<" partition geting\n";
        DAGPartition* curPart = partitions.at(pi);

        if(DFSFindPartitionCycle(curPart))
        {
            errs()<<" cycle discovered quit quit\n";
            // now see which partitions are in the cycle
            for(unsigned int pie = 0; pie < partitions.size(); pie++)
            {
                    DAGPartition* curParte = partitions.at(pie);
                    if(curParte->cycleDetectCovered)
                    {
                        errs()<<"cycle contains "<<"\n";
                        curParte->print();
                        errs()<< "\n";
                    }
            }

            exit(1);
        }

    }
    errs()<<" no cycle discovered\n";
    // starting the actual generation of function
    for(unsigned int partInd = 0; partInd < partitions.size(); partInd++)
    {
        DAGPartition* curPart = partitions.at(partInd);
        DominatorTree* DT  = getAnalysisIfAvailable<DominatorTree>();
        PostDominatorTree* PDT = getAnalysisIfAvailable<PostDominatorTree>();
        curPart->generateBBList(DT, PDT);

        errs()<<"done part\n";
        errs()<<"[\n";
        std::vector<BasicBlock*>* AllBBs
                = allBBsInPartition[curPart];
        for(unsigned int allBBInd = 0; allBBInd < AllBBs->size(); allBBInd++)
        {
            errs()<<AllBBs->at(allBBInd)->getName();
            errs()<<"\n";
        }
        errs()<<"]\n";

    }
    // all BB list generated, lets check the partitions
    // now one by one we will generate the C code for each partition
    for(unsigned int partInd = 0; partInd < partitions.size(); partInd++)
    {
        DAGPartition* curPart = partitions.at(partInd);
        generateCFromBBList(curPart);
    }


}
bool PartitionGen::DFSFindPartitionCycle(DAGPartition* dp)
{

    if(dp->cycleDetectCovered)
        return true;


    dp->cycleDetectCovered = true;
    std::vector<DAGNode4Partition*>* curPartitionContent = &(dp->partitionContent);
    for(unsigned int ni = 0; ni < curPartitionContent->size();ni++)
    {
        DAGNode4Partition* curNode = curPartitionContent->at(ni);
        // for this curNode, we need to know its dependent nodes
        // then each of the dependent node will generate the next hop
        std::vector<DAGNode4Partition*> depNodes;
        findDependentNodes(curNode,dagNodeMap,depNodes);
        for(unsigned int di =0 ; di<depNodes.size(); di++)
        {
            DAGNode4Partition* nextNode=depNodes.at(di);

            DAGPartition* nextHop = dagPartitionMap[nextNode];
            if(nextHop==dp)
                continue;
            if(DFSFindPartitionCycle(nextHop))
            {
                return true;
            }
        }

    }
    dp->cycleDetectCovered = false;
    return false;
}

void PartitionGen::generateCFromBBList(DAGPartition* pa)
{
    //BBMap2Ins& srcBBs, BBMap2Ins& insBBs, std::vector<BasicBlock*>& BBList
    BBMap2Ins* srcBBs = srcBBsInPartition[pa];
    BBMap2Ins* insBBs = insBBsInPartition[pa];
    std::vector<BasicBlock*>* BBList = allBBsInPartition[pa];
    // we can generate the definition string, and create a mapping of instruction to def string
    InsMap2Str ins2Def;



    BBMap2outStr bb2Str;
    for(unsigned int curBBInd = 0; curBBInd < BBList-size(); curBBInd++)
    {
        BasicBlock* curBB = BBList->at(curBBInd);
        std::vector<std::string>* curBBStrArray = new std::vector<std::string>();
        bb2Str[curBB] = curBBStrArray;

        std::string bbname = replaceAllDotWUS( curBB->getName());
        bbname.append(":\n");
        curBBStrArray->push_back(bbname);

        if(srcBBs->find(curBB)==srcBBs->end() && insBBs->find(curBB)==insBBs->end())
        {
            // basicblock takes in a branch tag only -- definitely not sending stuff to remote
            Instruction* curTerm = curBB->getTerminator();
            std::string termStr = generateSingleStatement(curTerm,true,false,ins2Def);
            curBBStrArray->push_back(termStr);
            continue;
        }
        std::vector<Instruction*>* srcIns = 0;
        std::vector<Instruction*>* actualIns = 0;
        if(srcBBs.find(curBB)!=srcBBs.end())
            srcIns = srcBBs[curBB];

        if(insBBs.find(curBB)!=insBBs.end())
            actualIns = insBBs[curBB];


        for(BasicBlock::iterator insPt = curBB->begin(), insEnd = curBB->end(); insPt != insEnd; insPt++)
        {
            if(srcIns!=0 && !(std::find(srcIns->begin(),srcIns->end(), insPt)==srcIns->end()))
            {
                // this instruction is in the srcBB, meaning its output is used by this partition
                // meaning the we should insert a blocking read from FIFO

                std::string srcInsStr = generateSingleStatement(insPt,true,false,ins2Def);
                curBBStrArray->push_back(srcInsStr);
            }

            if(actualIns!=0 && !(std::find(actualIns->begin(),actualIns->end(),insPt)==actualIns->end()))
            {
                // this instruction is the actual, let's see if this ins is used by
                // instruction in other partition
                DAGPartition* curInsPart = getPartitionFromIns(insPt);
                // now check all its user to see if it is being used by others
                // if it is then we should also add an entry in the channel list
                // also if this is an terminator, it may not have any use?
                if(insPt->isTerminator())
                {

                    // are there other partitions having the same basicblock
                    for(unsigned sid = 0; sid < partitions.size(); sid++)
                    {
                        DAGPartition* destPart = partitions.at(sid);
                        std::vector<BasicBlock*>* destPartBBs = allBBsInPartition[destPart];
                        if(std::find(destPartBBs->begin(),destPartBBs->end(),curBB)!=destPartBBs->end())
                        {
                            //we need fanout
                        }
                    }
                }
                for(Value::use_iterator curUser = insPt->use_begin(), endUser = insPt->use_end(); curUser != endUser; ++curUser )
                {

                }


                std::string actualInsStr = generateSingleStatement(insPt,false,false,ins2Def);
                curBBStrArray->push_back(actualInsStr);
            }



        }
    }

    // now we can output


}
*/
// we have a data structure to map instruction to InstructionGraphNodes
// when we do the partitioning, we
bool PartitionGen::runOnFunction(Function &F) {


    int bbCount =0;

    for(Function::iterator bbi = F.begin(), bbe = F.end(); bbi!=bbe; ++bbi)
    {
        if(bbi->getName().size()==0)

        {
            std::stringstream ss;
            ss << "BB_Explicit_" <<bbCount;
            bbi->setName(ss.str());
            bbCount+=1;
        }
    }
    for(Function::iterator bbi = F.begin(), bbe = F.end(); bbi!=bbe; ++bbi)
    {
        errs()<<bbi->getName()<<"\n";
    }


    InstructionGraphNode* rootNode = getAnalysis<InstructionGraph>().getRoot();


    unsigned sccNum = 0;
    std::vector<DAGNode4Partition*> collectedDagNode;

    errs() << "SCCs for the program in PostOrder:"<<F.getName();
    for (scc_iterator<InstructionGraphNode*> SCCI = scc_begin(rootNode),
           E = scc_end(rootNode); SCCI != E; ++SCCI) {

      std::vector<InstructionGraphNode*> &nextSCC = *SCCI;
      // we can ignore the last scc coz its the pseudo node root
      if(nextSCC.at(0)->getInstruction()!=0 )
      {
          DAGNode4Partition* curDagNode = new DAGNode4Partition;
          curDagNode->init();
          curDagNode->dagNodeContent = new std::vector<InstructionGraphNode*>();
          *(curDagNode->dagNodeContent) = nextSCC;
          curDagNode->singleIns = (nextSCC.size()==1);

          for (std::vector<InstructionGraphNode*>::const_iterator I = nextSCC.begin(),
                 E = nextSCC.end(); I != E; ++I)
          {
              Instruction* curIns = (*I)->getInstruction();
              curDagNode->sccLat += instructionLatencyLookup(curIns);
              if(curIns->mayReadOrWriteMemory())
              {

                  curDagNode->hasMemory = true;
              }

              DAGNode4Partition *&IGN = this->dagNodeMap[curIns];
              IGN = curDagNode;

          }
          collectedDagNode.push_back(curDagNode);
      }



      /*errs() << "\nSCC #" << ++sccNum << " : ";
      for (std::vector<InstructionGraphNode*>::const_iterator I = nextSCC.begin(),
             E = nextSCC.end(); I != E; ++I)
      {
        if((*I)->getInstruction())
            errs() << *((*I)->getInstruction())<< "\n ";
        if (nextSCC.size() == 1 && SCCI.hasLoop())
            errs() << " (Has self-loop).";
      }*/
    }
    //errs()<<"here\n\n\n\n\n\n";
    std::reverse(collectedDagNode.begin(),collectedDagNode.end());
    // now the nodes are topologically shorted
    // let's check
    for(unsigned int dnInd =0; dnInd < collectedDagNode.size(); dnInd++)
    {
        DAGNode4Partition* curNode = collectedDagNode.at(dnInd);
        curNode->seqNum = dnInd;
    }
    for(unsigned int dnInd =0; dnInd < collectedDagNode.size(); dnInd++)
    {
        DAGNode4Partition* curNode = collectedDagNode.at(dnInd);
        std::vector<DAGNode4Partition*> myDep;
        findDependentNodes(curNode,this->dagNodeMap,myDep);
        // check every dep to make sure their seqNum is greater
        //errs()<<"my seq "<<curNode->seqNum<<" : my deps are ";
        for(unsigned depInd = 0; depInd<myDep.size(); depInd++)
        {
            //errs()<<myDep.at(depInd)->seqNum<<" ,";
            if(myDep.at(depInd)->seqNum < curNode->seqNum)
            {
                errs()<<"not topologically sorted\n";
                exit(1);

            }

        }
        errs()<<"\n";
    }





   /* for(unsigned int m=0; m <collectedDagNode.size(); m++)
    {
        //errs()<<m<<"node\n";
        DAGNode4Partition* curNode = collectedDagNode.at(m);
        const std::vector<InstructionGraphNode*> curNodeContent = *(curNode->dagNodeContent);
        //errs()<<curNodeContent.size()<<"\n";
        for (unsigned int mi=0; mi<curNodeContent.size();mi++)
        {
            if((curNodeContent.at(mi))->getInstruction())
              errs() << *((curNodeContent.at(mi))->getInstruction())<< "\n ";

        }
    }*/


    // all instructions have been added to the dagNodeMap, collectedDagNode
    // we can start building dependencies in the DAGNodePartitions
    // we can start making the partitions
    generatePartition(&collectedDagNode);
    // now all partitions are made
    // for each of these partitions, we will generate a control flow
    // before generating c function
    errs()<<"before check\n";
    generateControlFlowPerPartition();



    dagNodeMap.clear();
    dagPartitionMap.clear();
    // empty all the partitions
    for(unsigned k = 0; k<partitions.size(); k++)
    {
        delete partitions.at(k);
    }
    partitions.clear();
    for(unsigned k =0; k<collectedDagNode.size();k++)
    {
        delete collectedDagNode.at(k);
    }

    errs() << "\n";







  return true;
}

