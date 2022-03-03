#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/User.h"
# include "llvm/ADT/StringRef.h" 

#include <iostream>
#include <string>

#include "llvm/DebugInfo/PDB/Native/HashTable.h"
#include "llvm/ADT/Optional.h"
#include "llvm/DebugInfo/PDB/Native/RawError.h"
#include "llvm/Support/BinaryStreamReader.h"
#include "llvm/Support/BinaryStreamWriter.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/MathExtras.h"

#include <string>

using namespace llvm;
using namespace std;

#define DEBUG_TYPE "ValueNumbering"

using namespace llvm;

namespace {
struct ValueNumbering : public FunctionPass {
    string func_name = "test3";
    static char ID;
    ValueNumbering() : FunctionPass(ID) {}

    int superscript = 1; // value
    std::map<string,int> LVN_hash_table;

    std::string checkConstant(User *checkConst){
        std::string currConstant;   
        for (auto it = checkConst->op_begin(); it != checkConst->op_end(); ++it) {                        
            // check constant
            if(isa<ConstantInt>(it)){
                auto* constantValls = dyn_cast<ConstantInt>(it);
                currConstant = std::to_string(constantValls->getSExtValue());  
            }                         
        }
        return currConstant;
    }

    void updateHashtTable(std::string operation, int currSup){
        std::map<string, int>::iterator it = LVN_hash_table.find(operation); 
            if (it != LVN_hash_table.end())
                it->second = currSup;
    }
    
    int getSuperscript(std::string operation){
        int sup = superscript;
        if(LVN_hash_table.count(operation)>0){
            sup = LVN_hash_table.at(operation);
        }else{ // if count== 0
            LVN_hash_table.insert(std::pair<std::string,int>(operation,sup));
            superscript = superscript +1;
        }
        return sup;
    }


    void generateStore(std::string currKey, std::string currConstant, std::string currName, int prevLoadSup){
        if(!currConstant.empty() && currConstant.size() > 0 ){ // if assign name with a constant
            int currSup = getSuperscript(currConstant);
            errs()  << currSup << " = " << currSup <<"\n";
           
            if(LVN_hash_table.count(currName) > 0){  // update assigned value with curr constant value
                updateHashtTable(currName,currSup); 
            }else{ // assgin non seen variable same as constant value
                LVN_hash_table.insert(std::pair<std::string,int>(currName,currSup));
            }

        }else{ // no constant
            if(LVN_hash_table.count(currName) == 0){ // initially assign
                if(!currKey.empty() && currKey.size() > 0 ){ // store operation result
                    LVN_hash_table.insert(std::pair<std::string,int>(currName,LVN_hash_table.at(currKey)));
                    errs()  << LVN_hash_table.at(currKey) << " = " << LVN_hash_table.at(currKey) <<"\n";
                    currKey = "";
                }else{ // store new 
                    int currSup = getSuperscript(currName);
                    errs()  << currSup << " = " << currSup <<"\n";
                }               
            }else{ // already in hash table
                if(!currKey.empty() && currKey.size() > 0 ){
                    int currSup = getSuperscript(currKey);
                    updateHashtTable(currName,currSup);
                    errs()  << LVN_hash_table.at(currKey) << " = " << LVN_hash_table.at(currKey) <<"\n";
                    currKey = "";
                }else{
                    int currSup = prevLoadSup;
                    updateHashtTable(currName,prevLoadSup);
                    errs()  << prevLoadSup << " = " << prevLoadSup <<"\n";
                }             
            }
        }
    }


    bool runOnFunction(Function &F) override {
        
        errs() << "ValueNumbering: " << F.getName() << "\n";
        if (F.getName() != func_name) return false;

        for (auto& basic_block : F)
        {
            LVN_hash_table.clear();

            // operation varibale: a <- x + y
            // operation name: +, *
            std::string Key="";
            std::string op_name="";
            std::string store_name="";
            std::string op_1="";
            std::string op_2="";

            int store_val;
            int op_1_val;
            int op_2_val;
            int load_sup;

            for (auto& inst : basic_block)
            {
                errs() << inst << "\n";
                if(inst.getOpcode() == Instruction::Load){
                    errs() << "This is Load"<<"\n";
                    std::string load_name = ((*inst.getOperand(0)).getName()).str();
                    load_sup = LVN_hash_table.at(load_name);
                    errs()  <<  load_sup << " = " << load_sup <<"\n";
                }
                if(inst.getOpcode() == Instruction::Store){
                    errs() << "This is Store"<<"\n";
                    // assign new ID or update superscrption
                    auto* ptrConst = dyn_cast<User>(&inst);
                    std::string currConstant = checkConstant(ptrConst);
                    store_name = ((*inst.getOperand(1)).getName()).str();
                    generateStore(Key,currConstant,store_name,load_sup);
                    // check with load val
                    Key = "";
                }
                if (inst.isBinaryOp())
                {
                    errs() << "Op Code:" << inst.getOpcodeName()<<"\n";
                    if(inst.getOpcode() == Instruction::Add){
                        errs() << "This is Addition BinaryOp"<<"\n";
                        op_name = "+";
                    }
                    if(inst.getOpcode() == Instruction::Sub){
                        errs() << "This is Substrction BinaryOp"<<"\n";
                        op_name = "-";
                    }
                    if(inst.getOpcode() == Instruction::Mul){
                        errs() << "This is Multiplication BinaryOp"<<"\n";
                        op_name = "*";
                    }
                    
                    // see other classes, Instruction::Sub, Instruction::UDiv, Instruction::SDiv
                    // errs() << "Operand(0)" << (*inst.getOperand(0))<<"\n";
                    auto* ptr = dyn_cast<User>(&inst);
                    int count = 0;
                    //errs() << "\t" << *ptr << "\n";
                    for (auto it = ptr->op_begin(); it != ptr->op_end(); ++it) {
                        errs() << "\t" <<  *(*it) << "\n";
                        llvm::User *currIns = dyn_cast<User>(it);
                        if (count == 0){
                            // check constant
                            if(isa<ConstantInt>(it)){
                                auto* constantVal = dyn_cast<ConstantInt>(it);
                                std::string currConstant = std::to_string(constantVal->getSExtValue());
                                op_1 = currConstant;
                                op_1_val = getSuperscript(currConstant);
                            }else{
                                op_1 = (currIns->getOperand(0)->getName()).str();
                                op_1_val = LVN_hash_table.at(op_1);
                            }                           
                        }
                        if (count == 1){
                            // check constant
                            if(isa<ConstantInt>(it)){
                                auto* constantVal = dyn_cast<ConstantInt>(it);
                                std::string currConstant = std::to_string(constantVal->getSExtValue());
                                op_2 = currConstant;
                                op_2_val = getSuperscript(currConstant);
                            }else{
                                op_2 = (currIns->getOperand(0)->getName()).str();
                                op_2_val = LVN_hash_table.at(op_2);
                            }  
                        }
                        count++; 
                        // if ((*it)->hasName()) 
                        // errs() << (*it)->getName() << "\n";                      
                    }
                    // assign variable Key <- a+b
                        Key = std::to_string(op_1_val) + op_name + std::to_string(op_2_val);
                        if(LVN_hash_table.count(Key) > 0){
                            errs() << LVN_hash_table.at(Key)<< " = ";
                            errs()  << Key << "  (Redundant)" ;
                        }
                        else{
                            errs() << superscript << " = " << Key ;
                            LVN_hash_table.insert(std::pair<std::string,int>(Key,superscript));
                            superscript = superscript + 1;
                        }
                    
                    errs() << "\n";
                } // end if
                errs() << "----------------------" << "\n";
            } // end for inst
        } // end for block
        return false;
    } // end runOnFunction
}; // end of struct ValueNumbering
}  // end of anonymous namespace

char ValueNumbering::ID = 0;
static RegisterPass<ValueNumbering> X("ValueNumbering", "ValueNumbering Pass",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);
