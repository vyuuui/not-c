#include <cassert>
#include <any>
#include <iostream>
#include <string>
#include <sstream>
#include <fstream>
#include <list>
#include <stack>
#include <unordered_map>
#include <memory>
#include <vector>


/*
32 64-bit regs r0-r31

move t0, r0

Copy operations:
mov (mem/reg) (mem/reg)

Math operations:
add (mem/reg) (mem/reg) (mem/reg)
sub (mem/reg) (mem/reg) (mem/reg)
mul
div
mod

Compare operations:
cmp (mem/reg) (mem/reg)

Jump operations:
jmp loc
jc (e, ne, gt, lt, ge, le) loc


add t0 r0 r1
add r3 r2 r0

*/

struct CpuContext {
    uint64_t program_counter;
   
   //http://www.unixwiz.net/techtips/x86-jumps.html
   
    bool compare_equal; // = true of r0 - r1 is == 0, otherwise false
    bool compare_overflow; // = true if r0 - r1 overflows
    bool compare_sign; // = true if r0 - r1 is < 0 (Signed)

    int64_t regstate[32];
    double regstate_float[32];
    std::stack<std::unordered_map<std::string, int64_t>> stacks;
    uint8_t cmp_flags;
} ctx;

enum class OperandType {
    Int8, Int16, Int32, Int64, Float
};

int64_t get_type_mask(OperandType type) {
    switch (type) {
        case OperandType::Int8:
            return 0xff;
            break;
        case OperandType::Int16:
            return 0xffff;
            break;
        case OperandType::Int32:
            return 0xffffffff;
            break;
        case OperandType::Int64:
            return 0xffffffffffffffff;
            break;
        case OperandType::Float:
            return 0xffffffffffffffff;
            break;
    }
    return 0;
}


class Operand {
public:
    Operand(OperandType type) : type(type) {}

    template <typename T>
    void set(T t) {
        int64_t as_generic = *reinterpret_cast<int64_t*>(&t);
        set_generic(as_generic & get_type_mask(type));
    }
    template <typename T>
    T get() {
        int64_t generic = get_generic() & get_type_mask(type);
        return *reinterpret_cast<T*>(&generic);
    }

    OperandType get_type() const {
        return type;
    }
private:
    virtual void set_generic(int64_t t) = 0;
    virtual int64_t get_generic() const = 0;
    
    OperandType type;
};

class MemoryOperand : public Operand {
public:
    MemoryOperand(OperandType type, std::string const& var_name) : Operand(type), var_name(var_name) {}
    
    void set_generic(int64_t value) override {
        ctx.stacks.top()[var_name] = value;
    }
    
    int64_t get_generic() const override {
        return ctx.stacks.top()[var_name];
    }

private:
    std::string var_name;
};

class IntRegisterOperand : public Operand {
public:
    IntRegisterOperand(OperandType type, uint8_t register_num) : Operand(type), register_num(register_num) {
        if (register_num >= 32) {
            throw "Invalid integer register number";
        }
    }

    void set_generic(int64_t t) override {
        ctx.regstate[register_num] = t;
    }

    int64_t get_generic() const override {
        return ctx.regstate[register_num];
    }
private:
    uint8_t register_num;
};

class FloatRegisterOperand : public Operand {
public:
    FloatRegisterOperand(uint8_t register_num) : Operand(OperandType::Float), register_num(register_num) {
        if (register_num >= 32) {
            throw "Invalid float register number";
        }
    }

    void set_generic(int64_t t) override {
        ctx.regstate_float[register_num] = *reinterpret_cast<double*>(&t);
    }

    int64_t get_generic() const override {
        return *reinterpret_cast<int64_t*>(&ctx.regstate_float[register_num]);
    }
private:
    uint8_t register_num;
};

class ImmediateOperand : public Operand {
public:
    ImmediateOperand(OperandType type, int64_t value) : Operand(type), value(value) { }
    void set_generic(int64_t value) override {
        throw "Can't set an immediate!!!!\n";
    }
    int64_t get_generic() const override {
        return value;
    }
private:
    int64_t value;
};


class Instruction {
public:
    Instruction(std::vector<Operand*> ops) : operands(ops) {}
    virtual void execute(CpuContext& ctx) = 0;

    virtual ~Instruction() {
        for (Operand* operand : operands) {
            delete operand;
        }
    }
protected:
    std::vector<Operand*> operands;
};

enum class AsmCommand {
    Mov, Add, Sub, Mul, Div, Mod, Cmp, Jmp, Jcc, PushStack, PopStack
};


class MovInstruction : public Instruction {
public:
    using Instruction::Instruction;

    void execute(CpuContext& ctx) override {
        auto dest = operands[0];
        auto src = operands[1];
        switch (src->get_type()) {
            case OperandType::Float:
                dest->set<double>(src->get<double>());
                break;
            case OperandType::Int64:
            case OperandType::Int32:
            case OperandType::Int16:
            case OperandType::Int8:
                dest->set<int64_t>(src->get<int64_t>());
                break;
            break;
        }
    }
};

class AddInstruction : public Instruction {
public:
    using Instruction::Instruction;
    
    void execute(CpuContext& ctx) override {
        auto dest = operands[0];
        auto src1 = operands[1];
        auto src2 = operands[2];
        switch (src1->get_type()) {
            case OperandType::Float:
                dest->set<double>(src1->get<double>() + src2->get<double>());
                break;
            case OperandType::Int64:
            case OperandType::Int32:
            case OperandType::Int16:
            case OperandType::Int8:
                dest->set<uint64_t>(src1->get<uint64_t>() + src2->get<uint64_t>());
                break;
        }
    }
};

class SubInstruction : public Instruction {
public:
    using Instruction::Instruction;

    void execute(CpuContext& ctx) override {
        auto dest = operands[0];
        auto src1 = operands[1];
        auto src2 = operands[2];
        switch (src1->get_type()) {
            case OperandType::Float:
                dest->set<double>(src1->get<double>() - src2->get<double>());
                break;
            case OperandType::Int64:
            case OperandType::Int32:
            case OperandType::Int16:
            case OperandType::Int8:
                dest->set<uint64_t>(src1->get<uint64_t>() - src2->get<uint64_t>());
                break;
        }
    }
};

class MulInstruction : public Instruction {
public:
    using Instruction::Instruction;

    void execute(CpuContext& ctx) override {
        auto dest = operands[0];
        auto src1 = operands[1];
        auto src2 = operands[2];
        switch (src1->get_type()) {
            case OperandType::Float:
                dest->set<double>(src1->get<double>() * src2->get<double>());
                break;
            case OperandType::Int64:
            case OperandType::Int32:
            case OperandType::Int16:
            case OperandType::Int8:
                dest->set<uint64_t>(src1->get<uint64_t>() * src2->get<uint64_t>());
                break;
        }

    }
};

class DivInstruction : public Instruction {
public:
    using Instruction::Instruction;

    void execute(CpuContext& ctx) override {
        auto dest = operands[0];
        auto src1 = operands[1];
        auto src2 = operands[2];
        switch (src1->get_type()) {
            case OperandType::Float:
                dest->set<double>(src1->get<double>() / src2->get<double>());
                break;
            case OperandType::Int64:
            case OperandType::Int32:
            case OperandType::Int16:
            case OperandType::Int8:
                dest->set<uint64_t>(src1->get<uint64_t>() / src2->get<uint64_t>());
                break;
        }
    }
};

class ModInstruction : public Instruction {
public:
    using Instruction::Instruction;
    
    void execute(CpuContext& ctx) override {
        auto dest = operands[0];
        auto src1 = operands[1];
        auto src2 = operands[2];
        switch (src1->get_type()) {
            case OperandType::Float:
                std::cout << "fmod not supported\n";
                break;
            case OperandType::Int64:
            case OperandType::Int32:
            case OperandType::Int16:
            case OperandType::Int8:
                dest->set<uint64_t>(src1->get<uint64_t>() % src2->get<uint64_t>());
                break;
        }
    }
};

class CmpInstruction : public Instruction {
public:
    using Instruction::Instruction;
    
    void execute(CpuContext& ctx) override {
        auto src1 = operands[0];
        auto src2 = operands[1];
        switch (src1->get_type()) {
            case OperandType::Float:
                std::cout << "cmp with float not soup\n";
                break;
            case OperandType::Int64: {
                int64_t op1 = src1->get<int64_t>(), op2 = src2->get<int64_t>();
                int64_t result = op1 - op2;
                ctx.compare_sign = result < 0;
                ctx.compare_equal = result == 0;
                if (op1 > 0 && op2 > 0 && op1 + op2 < 0) {
                    ctx.compare_overflow = true;
                } else if (op1 < 0 && op2 < 0 && op1 + op2 > 0) {
                    ctx.compare_overflow = true;
                } else {
                    ctx.compare_overflow = false;
                }
                break;
            }
            case OperandType::Int32: {
                int32_t op1 = src1->get<int32_t>(), op2 = src2->get<int32_t>();
                int32_t result = op1 - op2;
                ctx.compare_sign = result < 0;
                ctx.compare_equal = result == 0;
                if (op1 > 0 && op2 > 0 && op1 + op2 < 0) {
                    ctx.compare_overflow = true;
                } else if (op1 < 0 && op2 < 0 && op1 + op2 > 0) {
                    ctx.compare_overflow = true;
                } else {
                    ctx.compare_overflow = false;
                }
                break;
            }
            case OperandType::Int16: {
                int16_t op1 = src1->get<int16_t>(), op2 = src2->get<int16_t>();
                int16_t result = op1 - op2;
                ctx.compare_sign = result < 0;
                ctx.compare_equal = result == 0;
                if (op1 > 0 && op2 > 0 && op1 + op2 < 0) {
                    ctx.compare_overflow = true;
                } else if (op1 < 0 && op2 < 0 && op1 + op2 > 0) {
                    ctx.compare_overflow = true;
                } else {
                    ctx.compare_overflow = false;
                }
                break;
            }
            case OperandType::Int8: {
                int8_t op1 = src1->get<int8_t>(), op2 = src2->get<int8_t>();
                int8_t result = op1 - op2;
                ctx.compare_sign = result < 0;
                ctx.compare_equal = result == 0;
                if (op1 > 0 && op2 > 0 && op1 + op2 < 0) {
                    ctx.compare_overflow = true;
                } else if (op1 < 0 && op2 < 0 && op1 + op2 > 0) {
                    ctx.compare_overflow = true;
                } else {
                    ctx.compare_overflow = false;
                }
                break;
            }
            break;
        }
    }
};

enum class JmpCondition {
    None, Eq, NotEq, Gt, Lt, Ge, Le
};

class JmpInstruction : public Instruction {
public:
    JmpInstruction(std::vector<Operand*> ops, JmpCondition condition = JmpCondition::None) : Instruction(ops), condition(condition) {}

    void execute(CpuContext& ctx) override {
        auto dest = operands[0];
        if (dest->get_type() == OperandType::Float) {
            throw "Fuck";
        }
        switch (condition) {
        case JmpCondition::None:
            ctx.program_counter += dest->get<int64_t>();
            break;
        case JmpCondition::Eq:
            if (ctx.compare_equal) {
                ctx.program_counter += dest->get<int64_t>();
            }
            break;
        case JmpCondition::NotEq:
            if (!ctx.compare_equal) {
                ctx.program_counter += dest->get<int64_t>();
            }
            break;
        case JmpCondition::Lt:
            if (ctx.compare_sign != ctx.compare_overflow) {
                ctx.program_counter += dest->get<int64_t>();
            }
            break;
        case JmpCondition::Le:
            if (ctx.compare_equal || ctx.compare_sign != ctx.compare_overflow) {
                ctx.program_counter += dest->get<int64_t>();
            }
            break;
        case JmpCondition::Ge:
            if (ctx.compare_sign == ctx.compare_overflow) {
                ctx.program_counter += dest->get<int64_t>();
            }
            break;
        case JmpCondition::Gt:
            if (ctx.compare_equal && ctx.compare_sign == ctx.compare_overflow) {
                ctx.program_counter += dest->get<int64_t>();
            }
            break;
        }
    }
private:
    JmpCondition condition;
};

class StackPush : public Instruction {
public:
    using Instruction::Instruction;
    
    void execute(CpuContext& ctx) override {
        ctx.stacks.push({});
    }
};

class StackPop : public Instruction {
public:
    using Instruction::Instruction;

    void execute(CpuContext& ctx) override {
        ctx.stacks.pop();
    }
};

class Print : public Instruction {
public:
    using Instruction::Instruction;

    void execute(CpuContext& ctx) override {
        auto src = operands[0];
         switch (src->get_type()) {
            case OperandType::Float:
                std::cout << src->get<double>() << std::endl;
                break;
            case OperandType::Int64:
            case OperandType::Int32:
            case OperandType::Int16:
            case OperandType::Int8:
                std::cout << src->get<uint64_t>() << std::endl;
                break;
        }
    }
};

Instruction* parseLine(std::istringstream stream) {
    std::string name, part;
    Instruction* ret = nullptr;
    if (std::getline(stream, name, ' ')) {
        std::vector<Operand*> ops;
        while (std::getline(stream, part, ' ')) {
            switch (part[0]) {
                case 'r': {
                    int regnum = strtol(part.data() + 1, nullptr, 10);
                    ops.push_back(new IntRegisterOperand(OperandType::Int64, regnum));
                    break;
                }
                case 'f': {
                    int regnum = strtol(part.data() + 1, nullptr, 10);
                    ops.push_back(new FloatRegisterOperand(regnum));
                    break;
                }
                case 't': {
                    OperandType type;
                    if (part.find("ti64") == 0) {
                        type = OperandType::Int64;
                    } else if (part.find("ti32") == 0) {
                        type = OperandType::Int32;
                    } else if (part.find("ti16") == 0) {
                        type = OperandType::Int16;
                    } else if (part.find("ti8") == 0) {
                        type = OperandType::Int8;
                    } else if (part.find("tf") == 0) {
                        type = OperandType::Float;
                    } else {
                        throw "Invalid memory operand prefix";
                    }
                    ops.push_back(new MemoryOperand(type, part));
                    break;
                }
                default: {
                    if (!isdigit(part[0])) {
                        throw "Immediate is not a value!";
                    }
                    size_t sz = part.size();
                    OperandType type;
                    std::string imm;
                    int64_t val;
                    if (part.find("i64") == (sz - 3)) {
                        type = OperandType::Int64;
                        imm = part.substr(0, sz - 3);
                        val = strtoll(imm.c_str(), 0, 10);
                    } else if (part.find("i32") == (sz - 3)) {
                        type = OperandType::Int32;
                        imm = part.substr(0, sz - 3);
                        val = static_cast<int32_t>(strtol(imm.c_str(), 0, 10));
                    } else if (part.find("i16") == (sz - 3)) {
                        type = OperandType::Int16;
                        imm = part.substr(0, sz - 3);
                        val = static_cast<int16_t>(strtol(imm.c_str(), 0, 10));
                    } else if (part.find("i8") == (sz - 2)) {
                        type = OperandType::Int8;
                        imm = part.substr(0, sz - 2);
                        val = static_cast<int8_t>(strtol(imm.c_str(), 0, 10));
                    } else if (part.find("f") == (sz - 1)) {
                        type = OperandType::Float;
                        imm = part.substr(0, sz - 1);
                        double val_d = strtod(imm.c_str(), nullptr);
                        val = *reinterpret_cast<uint64_t*>(&val_d);
                    }

                    ops.push_back(new ImmediateOperand(type, val));
                    break;
                }
            }
        }
        if (name == "mov") {
            ret = new MovInstruction(ops);
        } else if (name == "add") {
            ret = new AddInstruction(ops);
        } else if (name == "sub") {
            ret = new SubInstruction(ops);
        } else if (name == "mul") {
            ret = new MulInstruction(ops);
        } else if (name == "div") {
            ret = new DivInstruction(ops);
        } else if (name == "mod") {
            ret = new ModInstruction(ops);
        } else if (name == "cmp") {
            ret = new CmpInstruction(ops);
        } else if (name == "jmp") {
            ret = new JmpInstruction(ops);
        } else if (name == "je") {
            ret = new JmpInstruction(ops, JmpCondition::Eq);
        } else if (name == "jne") {
            ret = new JmpInstruction(ops, JmpCondition::NotEq);
        } else if (name == "jgt") {
            ret = new JmpInstruction(ops, JmpCondition::Gt);
        } else if (name == "jlt") {
            ret = new JmpInstruction(ops, JmpCondition::Lt);
        } else if (name == "jge") {
            ret = new JmpInstruction(ops, JmpCondition::Ge);
        } else if (name == "jle") {
            ret = new JmpInstruction(ops, JmpCondition::Le);
        } else if (name == "pushs") {
            ret = new StackPush(ops);
        } else if (name == "pops") {
            ret = new StackPop(ops);
        } else if (name == "print") {
            ret = new Print(ops);
        }
    }
    return ret;
}

void print_context() {
    std::cout << "Register state:\n";
    printf("PC = %d\n", ctx.program_counter);
    for (int i = 0; i < 2; i++) {
        for (int j = 0; j < 4; j++) {
            int idx = i * 4 + j;
            printf("r%d = %04d\t", idx, ctx.regstate[idx]);
            //std::cout << "r" << idx << " = " << ctx.regstate[idx] << "\t";
        }
        std::cout << "\n";
    }
    for (int i = 0; i < 2; i++) {
        for (int j = 0; j < 4; j++) {
            int idx = i * 4 + j;
            printf("f%d = %04f\t", idx, ctx.regstate_float[idx]);
            //std::cout << "f" << idx << " = " << ctx.regstate_float[idx] << "\t";
        }
        std::cout << "\n";
    }

    std::cout << "Stack state:\n";
    auto stacks_copy = ctx.stacks;
    int frame_level = 0;
    while (!stacks_copy.empty()) {
        std::cout << "Frame #" << frame_level << ":\n";
        auto const& frame = stacks_copy.top();
        for (auto&& [key, val] : frame) {
            std::cout << key << " = " << val << "\n";
        }
        frame_level++;
        stacks_copy.pop();
    }
}

int main() {
    std::ifstream asm_file;
    asm_file.open("file.asm");
    std::string line;
    std::vector<Instruction*> instructions;
    // INITIALIZE THE STACKS nat
    ctx.stacks.push({});
    while (std::getline(asm_file, line)) {
        auto instr = parseLine(std::istringstream{line});
        if (instr == nullptr) {
            std::cout << "Bad: " << line << std::endl;
        }
        instructions.push_back(instr);
    }
    std::cout << instructions.size() << std::endl;
    asm_file.close();
    try {
    while (ctx.program_counter < instructions.size()) {
        instructions[ctx.program_counter]->execute(ctx);
        ctx.program_counter++;
        //print_context();
        //std::cout << std::endl;
    }
    } catch (const char* err) {
        std::cout << "Error!" << err << std::endl;
    }
    return 0;
}

