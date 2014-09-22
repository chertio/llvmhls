#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "InstructionGraph.h"
#include "llvm/Support/Casting.h"
using namespace llvm;

InstructionGraph::InstructionGraph()
    : FunctionPass(ID), Root(0), ExternalInsNode(new InstructionGraphNode(0)) {
  initializeInstructionGraphPass(*PassRegistry::getPassRegistry());
}

void InstructionGraph::addToInstructionGraph(Instruction *I) {
  InstructionGraphNode *Node = getOrInsertInstruction(I);

  // If this function has external linkage, anything could call it.
  //if (!F->hasLocalLinkage()) {
  //  ExternalCallingNode->addCalledFunction(CallSite(), Node);

  // for all the instructions, we have the external instruction as
  // the ancestor
  ExternalInsNode->addDependentInstruction(Node);


  // Look for dependent instruction
  for(Value::use_iterator curUser = I->use_begin(), endUser = I->use_end(); curUser != endUser; ++curUser )
  {
      if(!isa<Instruction>(*curUser))
      {
          errs()<<"instruction used by non instruction\n";
          exit(1);
      }
      else
      {
           Node->addDependentInstruction(getOrInsertInstruction( cast<Instruction>(*curUser)));
      }
      //Node->addDependentInstruction(getOrInsertInstruction(curIns));
  }
  // we need to look at other kinda dependence --- memory?
  if(I->mayReadFromMemory())
  {
    //look at all other instructions who read the same memory segment
  }
  if(I->mayWriteToMemory())
  {

  }
}

void InstructionGraph::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
}

bool InstructionGraph::runOnFunction(Function &M) {
  Func = &M;

  ExternalInsNode = getOrInsertInstruction(0);
  //assert(!CallsExternalNode);
  //CallsExternalNode = new CallGraphNode(0);
  Root = ExternalInsNode;

  // Add every function to the call graph.

for (Function::iterator BB = M.begin(), BBE = M.end(); BB != BBE; ++BB)
  for(BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE; ++BI)
  {
       addToInstructionGraph(BI);
  }



  return false;
}

INITIALIZE_PASS(InstructionGraph, "basicig", "InstructionGraph Construction", false, true)

char InstructionGraph::ID = 0;
void InstructionGraph::releaseMemory() {
  /// CallsExternalNode is not in the function map, delete it explicitly.

  if (InstructionMap.empty())
    return;

// Reset all node's use counts to zero before deleting them to prevent an
// assertion from firing.
/*#ifndef NDEBUG
  for (InstructionMapTy::iterator I = InstructionMap.begin(), E = InstructionMap.end();
       I != E; ++I)
    I->second->allReferencesDropped();
#endif
*/
  for (InstructionMapTy::iterator I = InstructionMap.begin(), E = InstructionMap.end();
      I != E; ++I)
    delete I->second;
  InstructionMap.clear();
}


void InstructionGraph::print(raw_ostream &OS, const Function*) const {

  for (InstructionGraph::const_iterator I = begin(), E = end(); I != E; ++I)
    I->second->print(OS);
}
#if !defined(NDEBUG) || defined(LLVM_ENABLE_DUMP)
void InstructionGraph::dump() const {
  print(dbgs(), 0);
}
#endif

InstructionGraphNode *InstructionGraph::getOrInsertInstruction(const Instruction *F) {
  InstructionGraphNode *&IGN = InstructionMap[F];
  if (IGN) return IGN;

  assert((!F || F->getParent()->getParent()!= Func) && "instruction not in current function!");
  return IGN = new InstructionGraphNode(const_cast<Instruction*>(F));
}

void InstructionGraphNode::print(raw_ostream &OS) const {
  if (Instruction *myI = getInstruction())
    OS << *myI << "'";
  else
    OS << "external pesudo ins";

  OS << "<<" << this << ">>  #uses=" << DependentInstructions.size() << '\n';

  for (const_iterator I = begin(), E = end(); I != E; ++I) {
      OS << "  <" << I->second->getInstruction() << "> \n ";
  }
  OS << '\n';
}

#if !defined(NDEBUG) || defined(LLVM_ENABLE_DUMP)
void CallGraphNode::dump() const { print(dbgs()); }
#endif
