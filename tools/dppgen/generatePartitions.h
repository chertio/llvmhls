#ifndef GENPART_H
#define GENPART_H
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
#include "generateCInstruction.h"

#include "llvm/Analysis/Dominators.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/LoopInfo.h"
#include <vector>
#include <string>
#include <queue>
#define LONGLATTHRESHOLD 5
using namespace llvm;


    // each dag node is a cycle in the dependency graph
    struct DAGNode;
    // group of dag node
    struct DAGPartition;

    struct PartitionGen;

    static void generateCode(PartitionGen* pg, bool CPU_bar_HLS);



    typedef std::map<const Instruction *, DAGNode *> Insn2DagNodeMap;
    typedef std::map<const DAGNode*, DAGPartition*> DagNode2PartitionMap;

    // this is used for srcBB and insBB things
    // the basic block here is a basic block in a partition, which contains a subset
    // of the instructions in the original basic block
    typedef std::map<BasicBlock*, std::vector<Instruction*>*> BBMap2Ins;
    typedef std::map<DAGPartition*, BBMap2Ins*> partitionToBB2InsInfo;
    typedef std::map<DAGPartition*, std::vector<BasicBlock*>*> partitionToBBList;


    // we map instruction to tagName -- a string denoting the name of the channel
    //typedef std::map<Instruction*, std::string> InsMap2Str;




    // this is to keep track of the channels
    // we also map tagName to user Partition -- there can be multiple destination
    typedef std::map<std::string, std::vector<DAGPartition*>*> strMap2PartitionVector;

    typedef BBMap2Ins::iterator BBMapIter;
    static void addBBInsToMap(BBMap2Ins& map, Instruction* curIns)
    {
        BasicBlock* bbKey = curIns->getParent();
        BBMapIter I = map.find(bbKey);
        if(I== map.end())
        {
            std::vector<Instruction*>* curBBIns = new std::vector<Instruction*>();
            curBBIns->push_back(curIns);
            map[bbKey] = curBBIns;
        }
        else
        {
            std::vector<Instruction*>*& curBBIns = map[bbKey];
            // now check if it is already included
            if(std::find(curBBIns->begin(),curBBIns->end(),curIns )== curBBIns->end())
            {
                curBBIns->push_back(curIns);
            }
        }
    }

    static bool searchToBasicBlock(std::vector<BasicBlock*>& storage, BasicBlock* current, BasicBlock* target, BasicBlock* domInter )
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
            bool found = searchToBasicBlock(storage, curSuc, target,domInter);
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

    static BasicBlock* findDominator(BasicBlock* originalDominator,std::vector<BasicBlock*>* allBBs, DominatorTree* DT)
    {
        BasicBlock* dominator = originalDominator;
        for(unsigned int BBind = 0; BBind < allBBs->size(); BBind++)
        {
            BasicBlock* curBB = allBBs->at(BBind);
            if(dominator!=0)
                dominator = DT->findNearestCommonDominator(dominator, curBB);
            else
                dominator = curBB;
        }
        return dominator;
    }

    static BasicBlock* findDominator(BasicBlock* originalDominator,BBMap2Ins* mapOfBBs,DominatorTree* DT )
    {
        BasicBlock* dominator = originalDominator;
        for(BBMapIter bmi = mapOfBBs->begin(), bme = mapOfBBs->end(); bmi!=bme; ++bmi)
        {
            BasicBlock* curBB=bmi->first;
            if(dominator!=0)
                dominator = DT->findNearestCommonDominator(dominator, curBB);
            else
                dominator = curBB;
        }
        return dominator;
    }

    static BasicBlock* findPostDominator(BasicBlock* originalPostDominator,BBMap2Ins* mapOfBBs,PostDominatorTree* PDT )
    {
        BasicBlock* postDominator = originalPostDominator;
        for(BBMapIter bmi = mapOfBBs->begin(), bme = mapOfBBs->end(); bmi!=bme; ++bmi)
        {
            BasicBlock* curBB=bmi->first;
            if(postDominator!=0)
            {
                postDominator = PDT->findNearestCommonDominator(postDominator, curBB);

            }
            else
                postDominator = curBB;
        }
        return postDominator;
    }

    static void addPathToSelf(BasicBlock* curBB,std::vector<BasicBlock*>& AllBBs, BasicBlock* dominator)
    {
        int numSuc = curBB->getTerminator()->getNumSuccessors();
        std::vector<BasicBlock*> curPathStorage;
        for(int sucInd = 0; sucInd<numSuc; sucInd++)
        {
            BasicBlock* startBB=curBB->getTerminator()->getSuccessor(sucInd);
           // errs()<<"serach towards " << dest->getName()<<"\n";
            if(searchToBasicBlock(curPathStorage,startBB,curBB,dominator))
            {
                // got to put everything on the the AllBBs
                mergeInto(curPathStorage,AllBBs);
            }
            curPathStorage.clear();
        }
    }

    /*static bool recurseSearchRealBB(BasicBlock* curBB, BasicBlock* blockBB, BasicBlock* curTgt,std::vector<BasicBlock*>& seenBBs)
    {
        if(curBB == curTgt)
            return true;
        if(curBB == blockBB)
            return false;
        if(std::find(seenBBs.begin(),seenBBs.end(),curBB) != seenBBs.end())
            return false;
        seenBBs.push_back(curBB);
        // now traverse the successor of curBB
        TerminatorInst* ti = curBB->getTerminator();
        bool found = false;
        for(unsigned int sucInd = 0; sucInd < ti->getNumSuccessors(); sucInd++)
        {
            BasicBlock* curSuc = ti->getSuccessor(sucInd);

            found = recurseSearchRealBB(curSuc,blockBB,curTgt,seenBBs);
            if(found)
                return true;
        }
        return false;

    }
    // startBB is generally a flow only BB, pBlock is one of its postdominators/also a real BB
    static bool searchRealBBsWithoutBlock(BasicBlock* startBB, BasicBlock* pBlock, std::vector<BasicBlock*>& postDoms)
    {
        for(unsigned int rBBInd = 0; rBBInd < postDoms.size(); rBBInd++)
        {
            BasicBlock* curPDom = postDoms.at(rBBInd);
            if(pBlock == curPDom)
                    continue;
            // now we try to search for curPDom
            std::vector<BasicBlock*> seenBBs;
            bool found = recurseSearchRealBB(startBB,pBlock,curPDom,seenBBs);
            if(found)
                return true;
        }
        return false;
    }*/


    static void addPathBBsToBBMap(BBMap2Ins& dstBBs, BasicBlock* startBB, std::vector<BasicBlock*>& AllBBs,BasicBlock* domInter)
    {
        std::vector<BasicBlock*> curPathStorage;

        for(BBMapIter bmi = dstBBs.begin(), bme = dstBBs.end(); bmi!=bme; ++bmi)
        {


            BasicBlock* dest=bmi->first;
           // errs()<<"serach towards " << dest->getName()<<"\n";
            if(searchToBasicBlock(curPathStorage,startBB,dest, domInter))
            {
                // got to put everything on the the AllBBs
                mergeInto(curPathStorage,AllBBs);

            }
            curPathStorage.clear();

        }
    }

    static void addPhiOwner2Vector(std::vector<Instruction*>* curBBInsns, std::vector<BasicBlock*>* add2Vector)
    {
        for(unsigned int insInd = 0; insInd < curBBInsns->size(); insInd++)
        {
            Instruction* curIns = curBBInsns->at(insInd);
            if(isa<PHINode>(*curIns))
            {
                PHINode* curPhiIns = (PHINode*)(curIns);
                for(unsigned int inBlockInd = 0; inBlockInd<curPhiIns->getNumIncomingValues();inBlockInd++)
                {
                    BasicBlock* curPred = curPhiIns->getIncomingBlock(inBlockInd);
                    if(std::find(add2Vector->begin(),add2Vector->end(),curPred)==add2Vector->end())
                    {
                        //errs()<<"add real coz of phi "<<curPred->getName()<<"\n";
                        add2Vector->push_back(curPred);
                    }
                }
            }
        }

    }

    struct DAGNode{
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
      raw_ostream &Out;
      raw_ostream &fifoDes;
      bool NoCfDup;
      bool CPU_bar_HLS;
      Function* curFunc;
      partitionToBB2InsInfo srcBBsInPartition;
      partitionToBB2InsInfo insBBsInPartition;
      // each partition's bb list
      partitionToBBList allBBsInPartition;

      static int partGenId;

      strMap2PartitionVector channelFanOutPartition;


      //std::vector<DAGNode4Partition*> allDAGNodes;


      std::vector<DAGPartition*> partitions;

      // from instruction to node
      Insn2DagNodeMap dagNodeMap;
      // from node to partition
      DagNode2PartitionMap dagPartitionMap;

      PartitionGen(raw_ostream &out, raw_ostream &out2, bool noCfDup, bool cpuNotHLS) : FunctionPass(ID),Out(out),fifoDes(out2),NoCfDup(noCfDup),CPU_bar_HLS(cpuNotHLS){}
      bool runOnFunction(Function& func);

      void generatePartition(std::vector<DAGNode*> *dag);

      void generateControlFlowPerPartition();
      void print(raw_ostream &O, const Module* = 0) const { }

      /*void DFSCluster(DAGNode4Partition* curNode, DAGPartition* curPartition);
      void BFSCluster(DAGNode4Partition* curNode);*/
      void checkAcyclicDependency();
      void BarrierCluster(std::vector<DAGNode*> *dag);
      bool DFSFindPartitionCycle(DAGPartition* nextHop);

      virtual void getAnalysisUsage(AnalysisUsage &AU) const {
        AU.addRequired<InstructionGraph>();
        AU.addRequiredTransitive<DominatorTree>();
        AU.addRequired<PostDominatorTree>();
        AU.addRequired<LoopInfo>();
        AU.setPreservesAll();
      }
      DAGPartition* getPartitionFromIns(Instruction* ins)
      {
          DAGNode* node = dagNodeMap[const_cast<Instruction*>(ins)];
          DAGPartition* part = dagPartitionMap[const_cast<DAGNode*>(node)];
          return part;
      }
      void addChannelAndDepPartition(bool &thereIsPartitionReceiving, Instruction* insPt,
                                                   std::string& channelStr, DAGPartition* destPart, int channelType, int seqNum);


    };


    static void searchToFindKeeper(BasicBlock* curSeed, BasicBlock* curPred, BB2BBVectorMapTy* predMap,
                                   std::vector<BasicBlock*>& toKeep, std::vector<BasicBlock*>& allKeepers,
                                   std::vector<BasicBlock*>& seenBBs, PostDominatorTree* PDT, std::vector<BasicBlock*>* allBBs )
    {
        if(std::find(seenBBs.begin(), seenBBs.end(),curPred)!=seenBBs.end())
        {
            //already seen
            return;
        }
        // if not even in the partition, we dont care
        if(std::find(allBBs->begin(),allBBs->end(),curPred)==allBBs->end())
            return;

        // if it is already a keeper, then we stop
        if(std::find(toKeep.begin(),toKeep.end(),curPred)!=toKeep.end()  ||
                std::find(allKeepers.begin(),allKeepers.end(),curPred)!=allKeepers.end())
        {
            return;
        }

        if(! PDT->dominates(curSeed,curPred))
        {
            // this is a keeper
            toKeep.push_back(curPred);
            return;
        }
        else
        {
            // not a keeper, we continue
            seenBBs.push_back(curPred);
            if(predMap->find(curPred)!=predMap->end())
            {
                std::vector<BasicBlock*>* nextPreds = (*predMap)[curPred];

                for(unsigned int cPred = 0; cPred < nextPreds->size(); cPred++)
                {
                    BasicBlock* nextPred = nextPreds->at(cPred);
                    searchToFindKeeper(curSeed, nextPred,predMap, toKeep, allKeepers, seenBBs,PDT,allBBs );
                }
            }
        }
    }
    static void search4NextKeeper(BasicBlock* brSuccessor, std::vector<BasicBlock*>&allKeepers, std::vector<BasicBlock*>&curBranchKeeper,
                                  std::vector<BasicBlock*>&seenBBs, std::vector<BasicBlock*>&allBBs )
    {
        // seen it before, we return
        if(std::find(seenBBs.begin(),seenBBs.end(), brSuccessor)!=seenBBs.end())
            return;
        seenBBs.push_back(brSuccessor);
        // if this is outside current partition, its sort of a keeper...
        bool toAdd = false;
        if(std::find(allBBs.begin(),allBBs.end(),brSuccessor)==allBBs.end())
        {
            toAdd = true;
        }
        else if(std::find(allKeepers.begin(),allKeepers.end(),brSuccessor)!=allKeepers.end())
        {
            // we found a keeper
            toAdd = true;
        }

        if(toAdd)
        {
            if(std::find(curBranchKeeper.begin() ,curBranchKeeper.end() ,brSuccessor)==curBranchKeeper.end())
            {
                curBranchKeeper.push_back(brSuccessor);
            }
        }
        else
        {
            // start next hop
            TerminatorInst* termIns = brSuccessor->getTerminator();
            int numOutEdge = termIns->getNumSuccessors();
            if(numOutEdge==0)
            {
                // this is going nowhere, so it must be a keeper right?
                // lets say if it is not a keeper, it is a flow only block
                // why would a bb with no output be a flow only block? it cant
                // so it is not true -- this cannot happen
                errs()<<"a non-keeper exit block\n";
                exit(1);
            }
            for(unsigned int brInd = 0; brInd<numOutEdge; brInd++)
            {
                BasicBlock* nextSuccessor = termIns->getSuccessor(brInd);
                search4NextKeeper( nextSuccessor, allKeepers, curBranchKeeper, seenBBs, allBBs );
            }

        }
    }

    bool localDescendentAccessMemory(Instruction& curStep, std::vector<Instruction*>& seen, BBMap2Ins* curPartitionInsns)
    {
        if(std::find(seen.begin(),seen.end(),&curStep)!=seen.end())
            return false;
        seen.push_back(&curStep);


        errs()<<"\n--------------------\n";
        errs()<<curStep;
        errs()<<"\n--------------------\n";
        // if is in current
        BasicBlock* instOwner = curStep.getParent();
        if(curPartitionInsns->find(instOwner) == curPartitionInsns->end())
            return false;
        std::vector<Instruction*>* insWithSameOwner = curPartitionInsns->at(instOwner);
        if(std::find(insWithSameOwner->begin(),insWithSameOwner->end(),&curStep)==insWithSameOwner->end() )
            return false;
        if(curStep.mayReadOrWriteMemory())
            return true;
        bool found = false;
        for(Value::use_iterator curUser = curStep.use_begin(), endUser = curStep.use_end(); curUser != endUser; ++curUser )
        {
            if(isa<Instruction>(*curUser))
            {

                found = localDescendentAccessMemory(*curUser,seen, curPartitionInsns);
                if(found)
                    return true;
            }
        }

        return false;
    }

    void addDuplicatedInstruction(std::vector<Instruction*>& duplicatedInstruction, Instruction* curIns,
                                  Insn2DagNodeMap& dnm, BBMap2Ins* srcBBs)
    {
        // find the dagNode corresponding to the instruction
        // it contains one scc of
        DAGNode* ownerNode = dnm[curIns];
        std::vector<InstructionGraphNode*>* allIGN =  ownerNode->dagNodeContent;
        // check if any instruction in allIGN contains memory, if there is , we dont
        // duplicate if there isnt
        if(ownerNode->hasMemory)
            return;
        if(ownerNode->sccLat < 5 && !ownerNode->singleIns)
        {
            // this is a potential candidate

            for(unsigned int insInd = 0; insInd = allIGN->size(); insInd++)
            {
                InstructionGraphNode* curIGN = allIGN->at(insInd);
                Instruction* curInsn = curIGN->getInstruction();
                errs()<<*curInsn;

            }
        }

    }

    struct DAGPartition{

        std::vector<BasicBlock*> singleSucBBs;
        // a partition contains a set of dagNode
        std::vector<DAGNode*> partitionContent;

        // let's add the pointer to the maps

        bool containMemory;
        bool containLongLatCyc;
        bool cycleDetectCovered;
        //DagNodeMapTy* insToDagNode;
        //DagPartitionMapTy* dagNodeToPartition;
        PartitionGen* top;
        // return instruction if it belongs here
        Instruction* rInsn;

        // so we have map from successorBB to destinationBB
        // so that in this partition, if somebody is branching to a successorBB,
        // we branch to the destinationBB instead.
        // to generate this, we ll need to replace earlier entries with later entries
        std::map<BasicBlock*,BasicBlock*> partitionBranchRemap;
        BasicBlock* dominator;
        void init(PartitionGen* tt )
        {
            containMemory = false;
            containLongLatCyc = false;
            cycleDetectCovered = false;
            top = tt;
            rInsn= NULL;
            dominator=0;
        }
        void print()
        {
            for(unsigned int nodeI = 0; nodeI < partitionContent.size(); nodeI++)
            {
                DAGNode* curNode = partitionContent.at(nodeI);
                curNode->print();
                errs()<<"\n";
            }
        }
        void addDagNode(DAGNode* dagNode,DagNode2PartitionMap &nodeToPartitionMap )
        {
            partitionContent.push_back(dagNode);
            dagNode->covered=true;
            containMemory |= dagNode->hasMemory;
            containLongLatCyc |= (dagNode->sccLat >= LONGLATTHRESHOLD);
            // each dagNode maps to  one partition
            nodeToPartitionMap[dagNode] = this;
        }
        void trimBBList()
        {
            BB2BBVectorMapTy* predMap = top->getAnalysis<InstructionGraph>().getPredecessorMap();
            PostDominatorTree* PDT = top->getAnalysisIfAvailable<PostDominatorTree>();
            //DominatorTree* DT= top->getAnalysisIfAvailable<DominatorTree>();
            // we can iterate through every block
            // in the allBBs list
            // if a basicblock A  is of no instruction --- only exist for flow
            // purpose, we then look at to see if it should be discarded
            // how do we do it?
            // all these are assumed to be redundant
            // we then have a queue of keepers -- starting from all realBBs,
            // we iterate until this queue is empty,
            // we take an iterm off this queue
            // traverse backward from it(currentR), for the path, if we
            // see a non real BB(nRBB), we check if currentR postdominate nRBB
            // if the answr is no, then nRBB is a keeper, the path is done,
            // and nRBB is added to the keeper queue,

            std::vector<BasicBlock*>* allBBs = (top->allBBsInPartition)[this];
            BBMap2Ins*  srcBBs = (top->srcBBsInPartition)[this];
            BBMap2Ins*  insBBs = (top->insBBsInPartition)[this];
            std::vector<BasicBlock*> allRealBBs;
            for(BBMapIter bmi = srcBBs->begin(), bme = srcBBs->end(); bmi!=bme; ++bmi)
            {
                BasicBlock* curBB=bmi->first;
                allRealBBs.push_back(curBB);

            }
            for(BBMapIter bmi = insBBs->begin(), bme = insBBs->end(); bmi!=bme; ++bmi)
            {
                BasicBlock* curBB=bmi->first;
                if(srcBBs->find(curBB)==srcBBs->end()) // if curBB was not in srcBB
                    allRealBBs.push_back(curBB);

                // now if this is generating a result based on incoming edges
                // then the basic block incoming edge should be counted as real
                // and always be preserved.
                std::vector<Instruction*>* curBBInsns = (*insBBs)[curBB];
                addPhiOwner2Vector(curBBInsns, &allRealBBs);

            }
            std::vector<BasicBlock*> toRemove = (*allBBs);


            // queue for blocks to keep
            std::vector<BasicBlock*> toKeep;
            std::vector<BasicBlock*> allKeepers;
            toKeep.insert(toKeep.begin(),allRealBBs.begin(),allRealBBs.end());

            while(toKeep.size()>0)
            {

                BasicBlock* curSeed = toKeep.back();
                toKeep.pop_back();
                allKeepers.push_back(curSeed);
                // search backwards from curSeed, until there is a keeper
                // all everything is seen
                std::vector<BasicBlock*> seenBBs;
                seenBBs.push_back(curSeed);

                if(predMap->find(curSeed)!=predMap->end())
                {
                    std::vector<BasicBlock*>* curPreds = (*predMap)[curSeed];

                    for(unsigned int cPred = 0; cPred < curPreds->size(); cPred++)
                    {
                        BasicBlock* curPred = curPreds->at(cPred);
                        searchToFindKeeper(curSeed, curPred,predMap, toKeep, allKeepers, seenBBs,PDT, allBBs );
                    }
                }

            }

            // we now try to build the remap
            // we start from one keeper, look for the next keeper in dfs way
            // realize every keeper is a divergent point
            // from a outgoing edge of an keeper, there can be only one keeper
            //this->partitionBranchRemap
            //errs()<<"======keeper=====\n";
            for(unsigned int keeperInd = 0; keeperInd < allKeepers.size();keeperInd++)
            {
                BasicBlock* curKeeper = allKeepers.at(keeperInd);
                //errs()<<curKeeper->getName()<<" ";
                TerminatorInst* termIns = curKeeper->getTerminator();
                int numOutEdge = termIns->getNumSuccessors();

                for(unsigned int brInd = 0; brInd<numOutEdge; brInd++)
                {
                    std::vector<BasicBlock*> curBranchKeeper;
                    // from this edge, we find next keeper
                    BasicBlock* brSuccessor = termIns->getSuccessor(brInd);
                    std::vector<BasicBlock*> seenBBs;
                    search4NextKeeper( brSuccessor, allKeepers, curBranchKeeper, seenBBs, *allBBs );

                    if(curBranchKeeper.size()>1)
                    {
                        errs()<<"more than one dest\n";
                        exit(1);
                    }
                    else if(curBranchKeeper.size()==0)
                    {
                        // this is an error coz if a keeper is branching somwhere but
                        // got nothing, something is wrong
                        errs()<<"no dest from keeper\n";
                        exit(1);
                    }
                    else
                    {
                        this->partitionBranchRemap[brSuccessor] = curBranchKeeper.at(0);
                    }

                }
                // now remove this keeper from toRemove
                std::vector<BasicBlock*>::iterator rmKeeperIter = std::find(toRemove.begin(),toRemove.end(),curKeeper);
                if(rmKeeperIter==toRemove.end())
                {
                    errs()<<"somehow not found\n";
                    exit(1);
                }
                    // must be found
                toRemove.erase(rmKeeperIter);

            }
            // now actually remove it
            for(unsigned int trind = 0; trind < toRemove.size(); trind++)
            {
                BasicBlock* bb2Remove = toRemove.at(trind);
                std::vector<BasicBlock*>::iterator found = std::find(allBBs->begin(),allBBs->end(),bb2Remove);
                errs()<<(*found)->getName()<<" removed " <<"\n";
                allBBs->erase(found);
            }
            // we shall build a map of basicblocks who now only have
            // one successor -- meaning they do not need to get remote branchtag
            // traverse every block, check their destination (with remap)
            // if it is a single

            for(unsigned int allBBInd=0; allBBInd<allBBs->size(); allBBInd++)
            {
                BasicBlock* curBB = allBBs->at(allBBInd);
                TerminatorInst* curTermInst = curBB->getTerminator();
                if(!isa<ReturnInst>(*curTermInst))
                {
                    int numSuc = curTermInst->getNumSuccessors();
                    bool sameDestDu2Remap = true;
                    BasicBlock* firstDst = curTermInst->getSuccessor(0);
                    if(partitionBranchRemap.find(firstDst)!=partitionBranchRemap.end())
                        firstDst = partitionBranchRemap[firstDst];
                    for(unsigned int i = 1; i<numSuc; i++)
                    {
                        BasicBlock* curDst = curTermInst->getSuccessor(i);
                        if(partitionBranchRemap.find(curDst)!=partitionBranchRemap.end())
                            curDst = partitionBranchRemap[curDst];
                        if(curDst!=firstDst)
                        {
                            sameDestDu2Remap = false;
                            break;
                        }

                    }
                    if(sameDestDu2Remap)
                        singleSucBBs.push_back(curBB);
                }
            }




        }
        // this is to be invoked right after the srcBB and insBB are established
        void optimizeBBByDup()
        {
            BBMap2Ins* srcBBs = top->srcBBsInPartition[this];
            BBMap2Ins* insBBs = top->insBBsInPartition[this];
            // now is there any way we can reduce the communication/or allow memory
            // optimization by duplicating simple counters
            // how do we do this?
            // we go through every srcBB, check, this srcBB probably belongs to a dependency cycle
            // -- if this srcBB feeds to an address, we want the address to be generated locally?
            // -- find the cycle,if it does not involve memory access, let's move it over
            // and check how many local src ins belong to this cycle, all them
            // get to become insBB
            // for now let's just dump out the involved instructions
            for(BBMapIter bmi = srcBBs->begin(), bme = srcBBs->end(); bmi!=bme; ++bmi)
            {
                std::vector<Instruction*>* curBBSrcInsns = bmi->second;
                // now for each of these instructions, we do a dfs to see if they fan out to local
                // instructions accessing memory
                // if yes, we search backwards to find the scc it depends on
                // how do we check if it is a counter structure?
                // there is a circle formed by an add instruction and a phiNode

                for(unsigned int insInd = 0; insInd < curBBSrcInsns->size(); insInd++)
                {
                    Instruction* curIns = curBBSrcInsns->at(insInd);
                    if(curIns->mayReadOrWriteMemory())
                        continue;
                    bool found = false;
                    std::vector<Instruction*> seenBBs;
                    for(Value::use_iterator curUser = curIns->use_begin(), endUser = curIns->use_end();
                        curUser != endUser; ++curUser )
                    {
                        if(isa<Instruction>(*curUser))
                        {
                            found = localDescendentAccessMemory(const_cast<Instruction>(*curUser),seenBBs,insBBs);
                            if(found)
                                break;
                        }
                    }
                    if(found)
                    {

                        errs()<<" found =============------------------======================\n";
                        // curIns fanning out to some memory instruction
                        // lets search backward --- this can be using the instruction graph structure
                        std::vector<Instruction*> duplicatedInstruction;

                        addDuplicatedInstruction(duplicatedInstruction, curIns,top->dagNodeMap,srcBBs);

                    }


                }
            }


        }

        void generateBBList()
        {
            // at this point instructions are associated with the partition
            // each of these instructions' owner bb is of course relevant to
            // to the partition
            // each of these instructions are getting operand from somewhere:
            // either instruction or function arg, if the source is an instruction I_s
            // then I_s' owner basic block would be relevant for this partition as well
            // each map keeps track of the BBs and the contained relevant instructions
            BBMap2Ins* sourceBBs = new BBMap2Ins;
            BBMap2Ins* insBBs = new BBMap2Ins;

            std::vector<Instruction*> srcInstructions;
            for(unsigned int nodeInd = 0; nodeInd < partitionContent.size(); nodeInd++)
            {
                DAGNode* curNode = partitionContent.at(nodeInd);
                for(unsigned int insInd = 0; insInd< curNode->dagNodeContent->size(); insInd++)
                {
                    Instruction* curIns = curNode->dagNodeContent->at(insInd)->getInstruction();
                    if(isa<ReturnInst>(*curIns))
                        rInsn= curIns;
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
            // dominator for src and ins BBs
            // this will be the first basicblock we need to convert
            // then we shall see where each bb diverge?

            DominatorTree* DT= top->getAnalysisIfAvailable<DominatorTree>();
            dominator = findDominator(dominator,sourceBBs,DT);
            dominator = findDominator(dominator,insBBs,DT);

            BasicBlock* postDominator =0;
            PostDominatorTree* PDT = top->getAnalysisIfAvailable<PostDominatorTree>();
            postDominator = findPostDominator(postDominator,sourceBBs,PDT);
            postDominator = findPostDominator(postDominator,insBBs,PDT);

            // start from each srcBBs, search backward until dominator,
            // everything in between is to be needed, -- if they are not srcBB nor insBBs
            // their terminator output would be needed? not necessariy!
            // if a properly contained BB (BB_z) -- meaning either src or ins BB
            // postdominate some BB (BB_x) which has nothing in it...BB_x
            // can be ommited -- all the edges going to BB_x can directly go
            // to BB_z
            // how do we detect this?
            // originally, we start from the dominator, then search to every BB
            // adding everything in the path, this dominator's terminator is
            // necessarily produced by an earlier stage due to the transitive dominance
            // now -- we can start searching from dominator to a destination BB,
            // if at a certain point, a particular BB is properly postdominated
            // by the destination BB, then we can directly go from the precedessors
            // of this BB to the destination BB -- without adding any BBs in between
            //
            // how do we know where to branch to?
            // we shall have a map, the first ommited BB would be the key
            // pointing to the postdominator, this postdominator (destination)
            // can be changed, for instance, originally we set the postdominator
            // to be A, then later we search for B and found the omitted BB
            // for A --- then either A dominate B or B dominate A, we will
            // make the earlier one the value of our table, and then add
            // entries for the path between A and B/B and A
            //



            // in the case of two BBs, if one BB is never reaching another BB
            // without going through dominator, then when this BB exits, we can
            // just wait in the dominator, so the procedure should be use
            // each BB as starting point to search for all other BBs, if any BB
            // is found all path to that BB should be included? if none can be found
            // then getting out of this BB is same as getting out of our subgraph

            // naturally if we have everything within one BB, we just need that BB
            std::vector<BasicBlock*>* AllBBs = new std::vector<BasicBlock*>();
            // some of these BBs wont be in the map, in which case, we just need the terminator
            AllBBs->push_back(dominator);

            // add the path from the dominator to all the sourceBBs
            addPathBBsToBBMap(*sourceBBs,dominator,*AllBBs,dominator);
            addPathBBsToBBMap(*insBBs,dominator,*AllBBs,dominator);
            // now  we do the n^2 check to see if anybody goes to anybody else?
            for(BBMapIter bmi = sourceBBs->begin(), bme = sourceBBs->end(); bmi!=bme; ++bmi)
            {
                BasicBlock* curBB=bmi->first;
                //std::vector<BasicBlock*> curPathStorage;
                addPathBBsToBBMap(*sourceBBs,curBB,*AllBBs,dominator);
                addPathBBsToBBMap(*insBBs,curBB,*AllBBs,dominator);
                //searchToGroupAndAdd(curBB,dominator,*sourceBBs,curPathStorage,*AllBBs);
                // same thing for insBB
                //searchToGroupAndAdd(curBB,dominator,*insBBs,curPathStorage,*AllBBs);

            }
            for(BBMapIter bmi = insBBs->begin(), bme = insBBs->end(); bmi!=bme; ++bmi)
            {
                BasicBlock* curBB=bmi->first;
                //std::vector<BasicBlock*> curPathStorage;
                addPathBBsToBBMap(*sourceBBs,curBB,*AllBBs,dominator);
                addPathBBsToBBMap(*insBBs,curBB,*AllBBs,dominator);
                //searchToGroupAndAdd(curBB,dominator,*sourceBBs,curPathStorage,*AllBBs);
                // same thing for insBB
                //searchToGroupAndAdd(curBB,dominator,*insBBs,curPathStorage,*AllBBs);

                // now we shall look at the phi
                std::vector<Instruction*>* curBBInsns = bmi->second;
                addPhiOwner2Vector(curBBInsns, AllBBs);

            }

            // a special pass to search for every insBB and srcBB themselves
            // FIXME: because our search finishes when we see the destination
            // there is a case where we will generate wrong graph:
            // a BB (BB1) fans out to some other BBs then those BBs loop back to BB1
            // BB1 to those BBs and back will not be part of our control graph
            // but they should
            // this is fixed below as we start searchinf from every block's
            // successor
            for(BBMapIter bmi = insBBs->begin(), bme = insBBs->end(); bmi!=bme; ++bmi)
            {
                BasicBlock* curBB=bmi->first;
                // search all its successor
                addPathToSelf(curBB,*AllBBs,dominator);
            }
            for(BBMapIter bmi = sourceBBs->begin(), bme = sourceBBs->end(); bmi!=bme; ++bmi)
            {
                BasicBlock* curBB=bmi->first;
                addPathToSelf(curBB,*AllBBs,dominator);
            }



            LoopInfo* li =top->getAnalysisIfAvailable<LoopInfo>();
            if(!top->NoCfDup)
            {
                // we are going to duplicate control flows, this is to make sure we dont need while loops
                // and have the end of execution trackable
                // note at this point, any loop structure between the insBBs and srcBBs are already included

                /* to make sure everything exit the loops properly, we want our sub graphs to
                 * eventually branch to blocks outside of any loop, what we can do is to see what
                 * are the basic blocks outside of all the loops --> and trace from basic blocks in our
                 * list to these blocks, again a dfs --> keep a path if it hits something among this group
                 */
                if(li->getLoopDepth(dominator)!=0)
                {
                    // actual implementation, all the strongly connected basic blocks involving
                    // anybody in the AllBBs need to be included


                    //int sccNum=0;
                    std::vector<BasicBlock*> cpAllBBs = *AllBBs;
                    for(unsigned int existingBBInd = 0; existingBBInd < cpAllBBs.size(); existingBBInd++)
                    {
                        BasicBlock* curExistingBB = cpAllBBs.at(existingBBInd);
                        for (scc_iterator<Function*> SCCI = scc_begin(top->curFunc),
                               E = scc_end(top->curFunc); SCCI != E; ++SCCI)
                        {
                          std::vector<BasicBlock*> &nextSCC = *SCCI;
                          if(std::find(nextSCC.begin(),nextSCC.end(),curExistingBB)!=nextSCC.end())
                          {
                              // this scc should be included
                              mergeInto(nextSCC,*AllBBs);
                          }
                        }
                    }
                    dominator = findDominator(dominator,AllBBs,DT);

                }

            }

            // now all the basicblocks are added into the allBBs
            (top->srcBBsInPartition)[this]=sourceBBs;
            (top->insBBsInPartition)[this]=insBBs;
            (top->allBBsInPartition)[this]=AllBBs;


            // go to release memory here

        }




    };
    static bool needANewPartition(DAGPartition* curPartition, DAGNode* curNode)
    {
        if((curNode->hasMemory  &&  (curPartition->containLongLatCyc || curPartition->containMemory))||
           ((!curNode->singleIns  && curNode->sccLat >= LONGLATTHRESHOLD)&& (curPartition->containMemory)))
            return true;
        else
            return false;
    }
    static void findDependentNodes(DAGNode* curNode, Insn2DagNodeMap &nodeLookup, std::vector<DAGNode*> &depNodes)
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
                DAGNode* node2add = nodeLookup[curDepIns];
                depNodes.push_back(node2add);

            }
        }
    }





char PartitionGen::ID = 0;
int PartitionGen::partGenId = 0;
//static RegisterPass<PartitionGen>
//Y("dpp-gen", "generate decoupled processing functions for each function CFG");


bool compareDagNode(DAGNode* first, DAGNode* second)
{
    return first->seqNum < second->seqNum;
}



void PartitionGen::BarrierCluster(std::vector<DAGNode*> *dag)
{
    DAGPartition* curPartition = new DAGPartition;
    curPartition->init(this);
    partitions.push_back(curPartition);

    for(unsigned int dagInd = 0; dagInd < dag->size(); dagInd++)
    {

        DAGNode* curDagNode = dag->at(dagInd);
        curPartition->addDagNode(curDagNode,dagPartitionMap);
        // if this is not the last node and we need a new partition
        if(dagInd!=dag->size()-1 && needANewPartition(curPartition,curDagNode))
        {
            curPartition = new DAGPartition;
            curPartition->init(this);
            partitions.push_back(curPartition);
        }

    }
}


void PartitionGen::generatePartition(std::vector<DAGNode*> *dag)
{
    BarrierCluster(dag);
}
void PartitionGen::checkAcyclicDependency()
{
    // lets check if there is any cycle between the partitions

    for(unsigned int pi = 0; pi < partitions.size(); pi++)
    {
        errs()<<pi<<" partition geting\n";
        DAGPartition* curPart = partitions.at(pi);
        // dump partition content
        curPart->print();
        errs()<<"================\n";
        if(DFSFindPartitionCycle(curPart))
        {
            errs()<<" cycle discovered quit\n";
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

}


void PartitionGen::generateControlFlowPerPartition()
{
    // go through every partition, for each partition
    // go through all the instructions
    // for each instruction, find where their operands are from
    // then these are all the basic blocks we need
    // just a safety check here
    checkAcyclicDependency();

    // starting the actual generation of function
    //DominatorTree* DT  = getAnalysisIfAvailable<DominatorTree>();
    //PostDominatorTree* PDT = getAnalysisIfAvailable<PostDominatorTree>();




    for(unsigned int partInd = 0; partInd < partitions.size(); partInd++)
    {
        DAGPartition* curPart = partitions.at(partInd);

        curPart->generateBBList();
        curPart->optimizeBBByDup();
        curPart->trimBBList();
        errs()<<"done part "<<partInd <<"\n";
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

    generateCode(this,this->CPU_bar_HLS);


}
bool PartitionGen::DFSFindPartitionCycle(DAGPartition* dp)
{

    if(dp->cycleDetectCovered)
        return true;


    dp->cycleDetectCovered = true;
    std::vector<DAGNode*>* curPartitionContent = &(dp->partitionContent);
    for(unsigned int ni = 0; ni < curPartitionContent->size();ni++)
    {
        DAGNode* curNode = curPartitionContent->at(ni);
        // for this curNode, we need to know its dependent nodes
        // then each of the dependent node will generate the next hop
        std::vector<DAGNode*> depNodes;
        findDependentNodes(curNode,dagNodeMap,depNodes);
        for(unsigned int di =0 ; di<depNodes.size(); di++)
        {
            DAGNode* nextNode=depNodes.at(di);
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
void PartitionGen::addChannelAndDepPartition(bool &thereIsPartitionReceiving, Instruction* insPt,
                                             std::string& channelStr, DAGPartition* destPart,int channelType, int insSeqNum)
{
    if(!thereIsPartitionReceiving)
    {
        channelStr= generateChannelString(channelType,insSeqNum,insPt->getParent()->getName());
        //ins2Channel[insPt]= channelStr;

    }
    std::vector<DAGPartition*>*& channelToDestPartitions = channelFanOutPartition[channelStr];

    if(thereIsPartitionReceiving)
        errs()<<channelToDestPartitions->size()<<"\n";

    if(!thereIsPartitionReceiving)
        channelToDestPartitions = new std::vector<DAGPartition*>();

    channelToDestPartitions->push_back(destPart);
    thereIsPartitionReceiving=true;
}
// we have a data structure to map instruction to InstructionGraphNodes
// when we do the partitioning, we
bool PartitionGen::runOnFunction(Function &F) {
    // we want to make sure there is only one return instruction
    // coz if thats not the case, we may have multiple stages
    // all potentially return

    //  There is a pass (Unify Function Exit nodes i.e.,
    //-mergereturn <http://llvm.org/docs/Passes.html#mergereturn>) that
    //transform a function to have only 1 return instruction.

    bool seenReturnInst = false;
    curFunc = &F;

    int bbCount =0;

    for(Function::iterator bbi = F.begin(), bbe = F.end(); bbi!=bbe; ++bbi)
    {
        if(bbi->getName().size()==0)
        {
            std::string bbPrefix("BB_Explicit_");
            std::string bbIndStr = int2Str(bbCount);
            std::string newBbName = bbPrefix+bbIndStr;
            bbi->setName(newBbName);
            bbCount+=1;
        }
        else
        {
            std::string legal = replaceAllDotWUS(bbi->getName());

            bbi->setName(legal);
        }
        BasicBlock* curBB = &(*bbi);
        if(isa<ReturnInst>(*(curBB->getTerminator())))
        {
            if(seenReturnInst)
            {
                errs()<<"multiple return statement in the llvm cfg, dppgen does not work with multiple return blocks\n";
                errs()<<"There is a pass (Unify Function Exit nodes i.e.,-mergereturn <http://llvm.org/docs/Passes.html#mergereturn>) that transform a function to have only 1 return instruction.\n";
            }
            else
            {
                seenReturnInst = true;
            }
        }

    }





    InstructionGraphNode* rootNode = getAnalysis<InstructionGraph>().getRoot();

    std::vector<DAGNode*> collectedDagNode;
    // iterate through the sccs in our graph, each scc is a vector of
    // instructions -- some time a single instruction


    for (scc_iterator<InstructionGraphNode*> SCCI = scc_begin(rootNode),
           E = scc_end(rootNode); SCCI != E; ++SCCI) {

      std::vector<InstructionGraphNode*> &curSCC = *SCCI;
      // we can ignore the last scc coz its the pseudo node root
      if(curSCC.at(0)->getInstruction()!=0)
      {
          DAGNode* curDagNode = new DAGNode;
          curDagNode->init();
          curDagNode->dagNodeContent = new std::vector<InstructionGraphNode*>();

          // copy everything over
          *(curDagNode->dagNodeContent) = curSCC;
          curDagNode->singleIns = (curSCC.size()==1);

          for (std::vector<InstructionGraphNode*>::const_iterator I = curSCC.begin(),
                 E = curSCC.end(); I != E; ++I)
          {
              Instruction* curIns = (*I)->getInstruction();
              curDagNode->sccLat += instructionLatencyLookup(curIns);
              if(curIns->mayReadOrWriteMemory())
              {

                  curDagNode->hasMemory = true;
              }

              DAGNode *&IGN = this->dagNodeMap[curIns];
              IGN = curDagNode;

          }
          collectedDagNode.push_back(curDagNode);
      }
    }
    std::reverse(collectedDagNode.begin(),collectedDagNode.end());
    // now the nodes are topologically shorted
    // let's check
    for(unsigned int dnInd =0; dnInd < collectedDagNode.size(); dnInd++)
    {
        DAGNode* curNode = collectedDagNode.at(dnInd);
        curNode->seqNum = dnInd;
    }

    int totalNumOfIns=0 ;
    for(unsigned int dnInd =0; dnInd < collectedDagNode.size(); dnInd++)
    {
        DAGNode* curNode = collectedDagNode.at(dnInd);
        totalNumOfIns+= curNode->dagNodeContent->size();
        std::vector<DAGNode*> myDep;
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

    }


    errs()<<"total number of instructions in scc nodes "<<totalNumOfIns<<"\n";
    errs()<<"all scc nodes topologically sorted, continue\n";
    // all instructions have been added to the dagNodeMap, collectedDagNode
    // we can start building dependencies in the DAGNodePartitions
    // we can start making the partitions
    generatePartition(&collectedDagNode);
    // now all partitions are made
    // for each of these partitions, we will generate a control flow
    // before generating c function
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



#endif
