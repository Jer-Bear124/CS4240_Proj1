#include "ir.hpp"
#include "reaching_def.hpp"
#include "dead_code.hpp"
#include "ir_optimizer.hpp"
#include <fstream>
#include <algorithm>
#include <set>

std::shared_ptr<ircpp::IRProgram> IROptimizer::optimizeProgram(const ircpp::IRProgram& originalProgram) {
    auto optimizedProgram = std::make_shared<ircpp::IRProgram>();
    
    for (const auto& func : originalProgram.functions) {
        auto optimizedFunc = optimizeFunction(*func);

        bool changed;
        do {
            changed = false;

            ircpp::ControlFlowGraph cfg = ircpp::CFGBuilder::buildCFG(*optimizedFunc);
            DeadCodeResult deadCodeResult = analyzeDeadCode({cfg});
            const auto& deadCodeAnalysis = deadCodeResult.functionResults[0]["analysis"];

            int init_cnt = static_cast<int>(optimizedFunc->instructions.size());

            optimizedFunc->instructions = eliminateDeadInstructions(
                optimizedFunc->instructions,
                deadCodeAnalysis.deadInstructions);

            int end_cnt = static_cast<int>(optimizedFunc->instructions.size());

            if(init_cnt != end_cnt) changed = true;
        } while(changed);

        optimizedProgram->functions.push_back(optimizedFunc);
    }

    return optimizedProgram;
}

std::shared_ptr<ircpp::IRFunction> IROptimizer::optimizeFunction(const ircpp::IRFunction& originalFunction) {
    // Create a copy of the function
    auto optimizedFunction = std::make_shared<ircpp::IRFunction>(
        originalFunction.name,
        originalFunction.returnType,
        originalFunction.parameters,
        originalFunction.variables,
        originalFunction.instructions
    );
    
    return optimizedFunction;
}

void IROptimizer::writeOptimizedProgram(const ircpp::IRProgram& optimizedProgram, const std::string& filename) {
    // Use the new format approach
    writeOptimizedProgramNewFormat(optimizedProgram, filename);
}

void IROptimizer::writeOptimizedProgramNewFormat(const ircpp::IRProgram& optimizedProgram, const std::string& filename) {
    std::ofstream file(filename);
    if (!file.is_open()) {
        throw std::runtime_error("Cannot open file for writing: " + filename);
    }
    
    for (const auto& func : optimizedProgram.functions) {
        file << "#start_function" << std::endl;
        
        // Function signature
        if (func->returnType) {
            if (func->returnType == ircpp::IRIntType::get()) {
                file << "int ";
            } else {
                file << "float ";
            }
        } else {
            file << "void ";
        }
        
        file << func->name << "(";
        
        // Parameters
        for (size_t i = 0; i < func->parameters.size(); ++i) {
            if (i > 0) file << ", ";
            
            const auto& param = func->parameters[i];
            if (param->type == ircpp::IRIntType::get()) {
                file << "int " << param->getName();
            } else if (param->type == ircpp::IRFloatType::get()) {
                file << "float " << param->getName();
            } else if (auto arrayType = std::dynamic_pointer_cast<ircpp::IRArrayType>(param->type)) {
                if (arrayType->elementType == ircpp::IRIntType::get()) {
                    file << "int[" << arrayType->size << "] " << param->getName();
                } else {
                    file << "float[" << arrayType->size << "] " << param->getName();
                }
            }
        }
        
        file << "):" << std::endl;
        
        // Variable declarations - only include LOCAL variables, not parameters
        std::set<std::string> parameterNames;
        for (const auto& param : func->parameters) {
            parameterNames.insert(param->getName());
        }
        
        std::vector<std::string> intVars, floatVars;
        for (const auto& var : func->variables) {
            // Skip parameters - they're already declared in function signature
            if (parameterNames.find(var->getName()) != parameterNames.end()) {
                continue;
            }
            
            if (var->type == ircpp::IRIntType::get()) {
                intVars.push_back(var->getName());
            } else if (var->type == ircpp::IRFloatType::get()) {
                floatVars.push_back(var->getName());
            } else if (auto arrayType = std::dynamic_pointer_cast<ircpp::IRArrayType>(var->type)) {
                if (arrayType->elementType == ircpp::IRIntType::get()) {
                    intVars.push_back(var->getName() + "[" + std::to_string(arrayType->size) + "]");
                } else {
                    floatVars.push_back(var->getName() + "[" + std::to_string(arrayType->size) + "]");
                }
            }
        }
        
        // Always write int-list
        file << "int-list: ";
        for (size_t i = 0; i < intVars.size(); ++i) {
            if (i > 0) file << ", ";
            file << intVars[i];
        }
        file << std::endl;
        
        // Always write float-list
        file << "float-list: ";
        for (size_t i = 0; i < floatVars.size(); ++i) {
            if (i > 0) file << ", ";
            file << floatVars[i];
        }
        file << std::endl;
        
        // Instructions
        for (const auto& inst : func->instructions) {
            // Handle labels specially - they don't have indentation
            if (inst->opCode == ircpp::IRInstruction::OpCode::LABEL) {
                // Labels should be written as "labelname:" not "    label, labelname"
                if (!inst->operands.empty()) {
                    auto labelOp = std::dynamic_pointer_cast<ircpp::IRLabelOperand>(inst->operands[0]);
                    if (labelOp) {
                        file << labelOp->getName() << ":" << std::endl;
                    }
                }
                continue;
            }
            
            // Regular instructions with indentation
            file << "    ";
            
            switch (inst->opCode) {
                case ircpp::IRInstruction::OpCode::ASSIGN:
                    file << "assign, ";
                    break;
                case ircpp::IRInstruction::OpCode::ADD:
                    file << "add, ";
                    break;
                case ircpp::IRInstruction::OpCode::SUB:
                    file << "sub, ";
                    break;
                case ircpp::IRInstruction::OpCode::MULT:
                    file << "mult, ";
                    break;
                case ircpp::IRInstruction::OpCode::DIV:
                    file << "div, ";
                    break;
                case ircpp::IRInstruction::OpCode::AND:
                    file << "and, ";
                    break;
                case ircpp::IRInstruction::OpCode::OR:
                    file << "or, ";
                    break;
                case ircpp::IRInstruction::OpCode::GOTO:
                    file << "goto, ";
                    break;
                case ircpp::IRInstruction::OpCode::BREQ:
                    file << "breq, ";
                    break;
                case ircpp::IRInstruction::OpCode::BRNEQ:
                    file << "brneq, ";
                    break;
                case ircpp::IRInstruction::OpCode::BRLT:
                    file << "brlt, ";
                    break;
                case ircpp::IRInstruction::OpCode::BRGT:
                    file << "brgt, ";
                    break;
                case ircpp::IRInstruction::OpCode::BRGEQ:
                    file << "brgeq, ";
                    break;
                case ircpp::IRInstruction::OpCode::RETURN:
                    file << "return, ";
                    break;
                case ircpp::IRInstruction::OpCode::CALL:
                    file << "call, ";
                    break;
                case ircpp::IRInstruction::OpCode::CALLR:
                    file << "callr, ";
                    break;
                case ircpp::IRInstruction::OpCode::ARRAY_STORE:
                    file << "array_store, ";
                    break;
                case ircpp::IRInstruction::OpCode::ARRAY_LOAD:
                    file << "array_load, ";
                    break;
            }
            
            // Operands (skip for labels since we handled them above)
            for (size_t i = 0; i < inst->operands.size(); ++i) {
                if (i > 0) file << ", ";
                
                const auto& operand = inst->operands[i];
                if (auto varOp = std::dynamic_pointer_cast<ircpp::IRVariableOperand>(operand)) {
                    file << varOp->getName();
                } else if (auto constOp = std::dynamic_pointer_cast<ircpp::IRConstantOperand>(operand)) {
                    file << constOp->getValueString();
                } else if (auto funcOp = std::dynamic_pointer_cast<ircpp::IRFunctionOperand>(operand)) {
                    file << funcOp->getName();
                } else if (auto labelOp = std::dynamic_pointer_cast<ircpp::IRLabelOperand>(operand)) {
                    file << labelOp->getName();
                }
            }
            file << std::endl;
        }
        
        file << "#end_function" << std::endl;
        file << std::endl;
    }
    
    file.close();
}

std::vector<std::shared_ptr<ircpp::IRInstruction>> IROptimizer::eliminateDeadInstructions(
    const std::vector<std::shared_ptr<ircpp::IRInstruction>>& instructions,
    const std::unordered_set<int>& deadInstructions) {
    
    std::vector<std::shared_ptr<ircpp::IRInstruction>> optimizedInstructions;
    
    for (const auto& inst : instructions) {
        if (shouldKeepInstruction(*inst, deadInstructions)) {
            optimizedInstructions.push_back(inst);
        }
    }
    
    return optimizedInstructions;
}

bool IROptimizer::shouldKeepInstruction(const ircpp::IRInstruction& instruction, const std::unordered_set<int>& deadInstructions) {
    // Always keep certain instruction types that are essential for program functionality
    switch (instruction.opCode) {
        case ircpp::IRInstruction::OpCode::LABEL:
        case ircpp::IRInstruction::OpCode::GOTO:
        case ircpp::IRInstruction::OpCode::BREQ:
        case ircpp::IRInstruction::OpCode::BRNEQ:
        case ircpp::IRInstruction::OpCode::BRLT:
        case ircpp::IRInstruction::OpCode::BRGT:
        case ircpp::IRInstruction::OpCode::BRGEQ:
        case ircpp::IRInstruction::OpCode::RETURN:
        case ircpp::IRInstruction::OpCode::CALL:
        case ircpp::IRInstruction::OpCode::CALLR:
        case ircpp::IRInstruction::OpCode::ARRAY_STORE:  // CRITICAL: Array stores are essential!
            return true; // Keep control flow, function calls, and array operations
        default:
            break;
    }
    
    // Check if this instruction is marked as dead
    return deadInstructions.find(instruction.irLineNumber) == deadInstructions.end();
}
