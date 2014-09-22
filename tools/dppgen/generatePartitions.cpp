//===- PrintSCC.cpp - Enumerate SCCs in some key graphs -------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file provides passes to print out SCCs in a CFG or a CallGraph.
// Normally, you would not use these passes; instead, you would use the
// scc_iterator directly to enumerate SCCs and process them in some way.  These
// passes serve three purposes:
//
// (1) As a reference for how to use the scc_iterator.
// (2) To print out the SCCs for a CFG or a CallGraph:
//       analyze -print-cfg-sccs            to print the SCCs in each CFG of a module.
//       analyze -print-cfg-sccs -stats     to print the #SCCs and the maximum SCC size.
//       analyze -print-cfg-sccs -debug > /dev/null to watch the algorithm in action.
//
//     and similarly:
//       analyze -print-callgraph-sccs [-stats] [-debug] to print SCCs in the CallGraph
//
// (3) To test the scc_iterator.
//
//===----------------------------------------------------------------------===//

#include "llvm/ADT/SCCIterator.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/raw_ostream.h"
#include "InstructionGraph.h"
#include "generatePartitionsUtil.h"
#include <vector>
using namespace llvm;

namespace {
    struct DAGNode4Partition;

    struct DAGNode4Partition{
        const std::vector<InstructionGraphNode*>* dagNodeContent;
        bool singleIns;
        int sccLat;
        bool hasMemory;
        bool covered;

        void init()
        {
            singleIns = false;
            sccLat = 0;
            hasMemory = false;
            covered = false;
        }
    };

    struct DAGPartition{
        // a partition contains a set of dagNode
        std::vector<DAGNode4Partition> partitionContent;
        bool containMemory;
        bool containLongLatCyc;

        void init()
        {
            containMemory = false;
            containLongLatCyc = false;
        }

    };


  struct PartitionGen : public FunctionPass {
    static char ID;  // Pass identification, replacement for typeid

    //std::vector<DAGNode4Partition*> allDAGNodes;
    typedef std::map<const Instruction *, DAGNode4Partition *> DagNodeMapTy;
    typedef std::map<const DAGNode4Partition*, DAGPartition *> DagPartitionMapTy;

    std::vector<DAGPartition*> partitions;

    // from instruction to node
    DagNodeMapTy dagNodeMap;
    // from node to partition
    DagPartitionMapTy dagPartitionMap;

    PartitionGen() : FunctionPass(ID) {}
    bool runOnFunction(Function& func);

    void generatePartition(std::vector<DAGNode4Partition*> *dag);

    void print(raw_ostream &O, const Module* = 0) const { }

    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.addRequired<InstructionGraph>();
      AU.setPreservesAll();
    }




  };

}

char PartitionGen::ID = 0;
static RegisterPass<PartitionGen>
Y("dpp-gen", "generate decoupled processing functions for each function CFG");


void PartitionGen::DFSCluster(DAGNode4Partition* curNode, DAGPartition* curPartition)
{

}

void PartitionGen::generatePartition(std::vector<DAGNode4Partition*> *dag)
{
    DAGPartition* curPartition = 0;
    for(std::iterator di = dag->begin(), de = dag->end(); di!=de; ++di)
    {
        DAGNode4Partition* curNode = *di;
        if(curNode->covered)
            continue;

        if(!curPartition)
        {
            curPartition = new DAGPartition;
            curPartition->init();
            dag->push_back(curPartition);
        }
        // if curnode has memory or it is long latency cycle
        else if(curNode->hasMemory || (!curNode->singleIns  && curNode->sccLat >= 5))
        {
            if(curPartition->containLongLatCyc || curPartition->containMemory)
            {
                // time to start a new partition
                curPartition = new DAGPartition;
                curPartition->init();
                dag->push_back(curPartition);
            }

        }
        DFSCluster(curNode, curPartition);


    }
}

// we have a data structure to map instruction to InstructionGraphNodes
// when we do the partitioning, we
bool PartitionGen::runOnFunction(Function &F) {


    InstructionGraphNode* rootNode = getAnalysis<InstructionGraph>().getRoot();


    unsigned sccNum = 0;
    std::vector<DAGNode4Partition*> collectedDagNode;

    errs() << "SCCs for the program in PostOrder:";
    for (scc_iterator<InstructionGraphNode*> SCCI = scc_begin(rootNode),
           E = scc_end(rootNode); SCCI != E; ++SCCI) {

      const std::vector<InstructionGraphNode*> &nextSCC = *SCCI;
      // we can ignore the last scc coz its the pseudo node root
      if(nextSCC.at(0)->getInstruction()!=0 )
      {
          DAGNode4Partition* curDagNode = new DAGNode4Partition;
          curDagNode->init();
          curDagNode->dagNodeContent = &nextSCC;
          curDagNode->singleIns = (nextSCC.size()==1);

          for (std::vector<InstructionGraphNode*>::const_iterator I = nextSCC.begin(),
                 E = nextSCC.end(); I != E; ++I)
          {
              Instruction* curIns = (*I)->getInstruction();
              curDagNode->sccLat += instructionLatencyLookup(curIns);
              if(curIns->mayReadOrWriteMemory())
                  curDagNode->hasMemory = true;

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
    std::reverse(collectedDagNode.begin(),collectedDagNode.end());

    // all instructions have been added to the dagNodeMap, collectedDagNode
    // we can start building dependencies in the DAGNodePartitions
    // we can start making the partitions
    generatePartition(&collectedDagNode);

    errs() << "\n";







  return true;
}

