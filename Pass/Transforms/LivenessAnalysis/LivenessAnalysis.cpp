#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/IR/PassManager.h"

#include "llvm/Support/raw_ostream.h"

#include "llvm/IR/CFG.h"

using namespace std;

using namespace llvm;

namespace {

// This method implements what the pass does
void visitor(Function &F){

    // Here goes what you want to do with a pass
    
        string func_name = "test4";
        errs() << "LivenessAnalysis: " << F.getName() << "\n";
        
        // Comment this line
        if (F.getName() != func_name) return;
        
        std::map<string,std::set<string>> UEVAR_table; 
        std::map<string,std::set<string>> VARKILL_table; 
        
        // generate UEVAR
        // generate VAR KILL
        for (auto& basic_block_var : F)
        {
            std::string basic_block_name = basic_block_var.getName().str();
            std::set<string> uevar_List = {};
            std::set<string> varkill_List = {};

            errs() << "------------- " << basic_block_name << " ------------ " << "\n";

            for (auto& inst : basic_block_var)
            {
                // if load, add to UEVAR
                if(inst.getOpcode() == Instruction::Load && basic_block_name.compare("entry") != 0){
                    //errs() << "This is Load : UEVAR"<<"\n";
                    std::string load_name = ((*inst.getOperand(0)).getName()).str();
                    bool found = (std::find(varkill_List.begin(), varkill_List.end(), load_name) != varkill_List.end());
                    if(!found){
                        //errs()  <<  load_name <<"\n";
                        uevar_List.insert(load_name);
                        // todo: if already KILL, then not UEVAR
                    }
                }

                // if store, add to KILL
                if(inst.getOpcode() == Instruction::Store){
                    //errs() << "This is Store : KILL"<<"\n";             
                    std::string store_name = ((*inst.getOperand(1)).getName()).str();
                    //errs() << store_name <<"\n";
                    bool found = (std::find(varkill_List.begin(), varkill_List.end(), store_name) != varkill_List.end());
                    if(!found){
                        varkill_List.insert(store_name);
                    }
                }
                // if op, a <- c + d
                if (inst.isBinaryOp())
                {
                    std::string op_1;
                    std::string op_2;

                    bool op_1_const = false;
                    bool op_2_const = false;

                    auto* ptr = dyn_cast<User>(&inst);
                    int count = 0;
                    //errs() << "\t" << *ptr << "\n";
                    for (auto it = ptr->op_begin(); it != ptr->op_end(); ++it) {
                        // errs() << "\t" <<  *(*it) << "\n";
                        llvm::User *currIns = dyn_cast<User>(it);

                        if (count == 0){
                            // check constant
                            if(isa<ConstantInt>(it)){
                                auto* constantVal = dyn_cast<ConstantInt>(it);
                                std::string currConstant = std::to_string(constantVal->getSExtValue());
                                op_1_const = true;
                            }else{
                                op_1 = (currIns->getOperand(0)->getName()).str();
                            }                           
                        }
                        if (count == 1){
                            // check constant
                            if(isa<ConstantInt>(it)){ // ignore constant
                                auto* constantVal = dyn_cast<ConstantInt>(it);
                                std::string currConstant = std::to_string(constantVal->getSExtValue());
                                op_2_const = true;
                            }else{
                                op_2 = (currIns->getOperand(0)->getName()).str();
                            }  
                        }
                        count++; 
                        // if ((*it)->hasName()) 
                        // errs() << (*it)->getName() << "\n";  
                    } // end op loop

                    //errs() << "This is OP, UEVAR" << "\n";
                    // todo: if already KILL, then not UEVAR
                    if(!op_1_const){
                        bool found = (std::find(varkill_List.begin(), varkill_List.end(), op_1) != varkill_List.end());
                        if(!found){
                            //errs() << op_1 << "\n";
                            uevar_List.insert(op_1);
                        }
                    }
                    
                    if(!op_2_const){
                        bool found = (std::find(varkill_List.begin(), varkill_List.end(), op_2) != varkill_List.end());
                        if(!found){
                            //errs() << op_2 << "\n";
                            uevar_List.insert(op_2);
                        }
                    }                   
                } // end if op

            } // end one bb
            UEVAR_table.insert(std::pair<std::string,std::set<string>>(basic_block_name,uevar_List));
            VARKILL_table.insert(std::pair<std::string,std::set<string>>(basic_block_name,varkill_List));

            //errs() << " ----------- " << basic_block_name << " ---------------" << "\n";
            errs() << "UEVAR : ";
            std::set<std::string>::iterator itUevar;
            for ( auto itUevar = uevar_List.begin(); itUevar != uevar_List.end(); ++itUevar  )
            {
                errs() << (*itUevar) << ", ";
            } 
            errs() <<"\n";

            errs() << "KILL : ";
            std::set<std::string>::iterator itKill;
            for ( auto itKill = varkill_List.begin(); itKill != varkill_List.end(); ++itKill  )
            {
                errs()  << (*itKill) << ", ";
            } 
            errs() <<"\n";
        } // end all bb
        
        errs() << " ---------------- END CHECK ---------------" << "\n" << "\n";

        std::map<string,std::set<string>> LIVEOUT_table; 
        bool allSame; // check all list in hash table not change
        for (auto& basic_block : F)
        {
            // if ENTRY
            // OTHER
            // generate live out for predecessors, update

            errs() << basic_block.getName() << "\n";
            for (BasicBlock *Pred : predecessors(&basic_block)) {

                errs() << "This is pre_block check"<<"\n";
                errs() << Pred->getName() << "\n";
               
            }
            errs() << " -------- " << "\n";
         
        }
        
}


// New PM implementation
struct LivenessAnalysisPass : public PassInfoMixin<LivenessAnalysisPass> {

  // The first argument of the run() function defines on what level
  // of granularity your pass will run (e.g. Module, Function).
  // The second argument is the corresponding AnalysisManager
  // (e.g ModuleAnalysisManager, FunctionAnalysisManager)
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &) {
    visitor(F);
    return PreservedAnalyses::all();

    
  }
  
    static bool isRequired() { return true; }
};
}



//-----------------------------------------------------------------------------
// New PM Registration
//-----------------------------------------------------------------------------
extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
llvmGetPassPluginInfo() {
  return {
    LLVM_PLUGIN_API_VERSION, "LivenessAnalysisPass", LLVM_VERSION_STRING,
    [](PassBuilder &PB) {
      PB.registerPipelineParsingCallback(
        [](StringRef Name, FunctionPassManager &FPM,
        ArrayRef<PassBuilder::PipelineElement>) {
          if(Name == "liveness-analysis"){
            FPM.addPass(LivenessAnalysisPass());
            return true;
          }
          return false;
        });
    }};
}