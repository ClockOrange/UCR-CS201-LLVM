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
    
        string func_name = "test3";
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

            //errs() << "------------- " << basic_block_name << " ------------ " << "\n";

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
            // errs() << "UEVAR : ";
            // std::set<std::string>::iterator itUevar;
            // for ( auto itUevar = uevar_List.begin(); itUevar != uevar_List.end(); ++itUevar  )
            // {
            //     errs() << (*itUevar) << ", ";
            // } 
            // errs() <<"\n";

            // errs() << "KILL : ";
            // std::set<std::string>::iterator itKill;
            // for ( auto itKill = varkill_List.begin(); itKill != varkill_List.end(); ++itKill  )
            // {
            //     errs()  << (*itKill) << ", ";
            // } 
            // errs() <<"\n";
        } // end all bb
        
        //errs() << " ---------------- END CHECK ---------------" << "\n" << "\n";


       std::map<string,std::set<string>> LIVEOUT_table; 
        for (auto& basic_block : F)
        {
            std::set<string> liveout_list = {};
            std::string name = basic_block.getName().str();
            LIVEOUT_table.insert(std::pair<std::string,std::set<string>>(name,liveout_list));
        }
        bool Continue = true; // check all list in hash table not change
        while (Continue){
            Continue = false;

            for (auto& basic_block : F){
                std::set<string> new_liveout_list = {};

                //Union(Liveout(successor) - Killset(successor) + UEE(successor))
                for (BasicBlock *succ : successors(&basic_block)){
                    std::string succ_name = succ->getName().str();
                    std::set<string> kill;
                    std::set<string> uevar;
                    std::set<string> succ_liveout;
                    std::map<string,std::set<string>>::iterator search_succ;

                    search_succ = UEVAR_table.find(succ_name);
                    uevar = search_succ->second;
                    search_succ = VARKILL_table.find(succ_name);
                    kill = search_succ->second;
                    search_succ = LIVEOUT_table.find(succ_name);
                    succ_liveout = search_succ->second;

                    std::set<string> temp;
                    set_difference(succ_liveout.begin(),succ_liveout.end(),kill.begin(),kill.end(),inserter(temp,temp.begin()));
                    std::set<string> temp2;
                    set_union(temp.begin(),temp.end(),uevar.begin(),uevar.end(),inserter(temp2,temp2.begin()));
                    std::set<string> temp3;
                    set_union(temp2.begin(),temp2.end(),new_liveout_list.begin(),new_liveout_list.end(),inserter(temp3,temp3.begin()));
                    new_liveout_list = temp3;
                }

                std::map<string,std::set<string>>::iterator search_block;
                std::string name = basic_block.getName().str();
                search_block = LIVEOUT_table.find(name);

                std::set<string> old;
                old = search_block->second;
                LIVEOUT_table[name] = new_liveout_list;
                
                if (old != new_liveout_list)
                {
                    Continue = true;

                }

            }
        }


        for (auto& basic_block : F)
        {
            // if ENTRY
            // OTHER
            // generate live out for predecessors, update

            errs() << "----- " << basic_block.getName() << " -----"<< "\n";
            std::map<string,std::set<string>>::iterator search_bb;
            search_bb = LIVEOUT_table.find(basic_block.getName().str());
            std::set<string> x;
            x = search_bb->second;


            std::map<string,std::set<string>>::iterator uevar_bb;
            uevar_bb = UEVAR_table.find(basic_block.getName().str());
            std::set<string> uevar_List;
            uevar_List = uevar_bb->second;
            errs() << "UEVAR : ";
            std::set<std::string>::iterator itUevar;
            for ( auto itUevar = uevar_List.begin(); itUevar != uevar_List.end(); ++itUevar  )
            {
                errs() << (*itUevar) << " ";
            } 
            errs() <<"\n";

            std::map<string,std::set<string>>::iterator kill_bb;
            kill_bb = VARKILL_table.find(basic_block.getName().str());
            std::set<string> varkill_List;
            varkill_List = kill_bb->second;
            errs() << "VARKILL : ";
            std::set<std::string>::iterator itKill;
            for ( auto itKill = varkill_List.begin(); itKill != varkill_List.end(); ++itKill  )
            {
                errs()  << (*itKill) << " ";
            } 
            errs() <<"\n";

            errs() << "LIVEOUT : ";
            std::set<std::string>::iterator it=x.begin();
            while(it!=x.end()){
                errs() << (*it) << " ";
                it++;
            }
            errs() <<"\n";

            //errs() << " -------- " << "\n";
         
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