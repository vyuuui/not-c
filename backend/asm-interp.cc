#include <cassert>
#include <cstring>
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
#include <optional>
#include <regex>
#include <stdexcept>

constexpr size_t kPrimitiveMaxSize = 8;

void trim_whitespace(std::string& str) {
    int left = 0, right = str.size() - 1;
    for (; left < str.size(); left++) {
        if (!isspace(str[left])) {
            break;
        }
    }
    for (; right >= 0; right--) {
        if (!isspace(str[right])) {
            break;
        }
    }
    if (left >= right) {
        str = "";
    } else {
        str = str.substr(left, right - left + 1);
    }
}

void getline_trim(std::ifstream& stream, std::string& out) {
    std::getline(stream, out);
    trim_whitespace(out);
}

class ProgramStack {
public:
    void* get_stack_var(int64_t byte_off) {
        return static_cast<void*>(frame_data.data() + byte_off);
    }
    void push_stack_var(void* val, size_t size) {
        int64_t offset = get_stack_size();
        change_size(size);
        set_stack_var(offset, val, size);
    }
    void set_stack_var(int64_t byte_off, void* val, size_t size) {
        std::memcpy(frame_data.data() + byte_off, val, size);
    }
    size_t get_stack_size() {
        return frame_data.size();
    }
    void change_size(ssize_t change) {
        frame_data.resize(frame_data.size() + change);
    }

private:
    std::vector<uint8_t> frame_data;
};

enum class BaseType {
    Int8, Int16, Int32, Int64, Float, Void
};

BaseType type_from_string(std::string const& str) {
    if (str == "int8") {
        return BaseType::Int8;
    } else if (str == "int16") {
        return BaseType::Int16;
    } else if (str == "int32") {
        return BaseType::Int32;
    } else if (str == "int64") {
        return BaseType::Int64;
    } else if (str == "float") {
        return BaseType::Float;
    }
    return BaseType::Void;
}

size_t base_type_size(BaseType base_type) {
    switch (base_type) {
        case BaseType::Int8:
        return 1;
        case BaseType::Int16:
        return 2;
        case BaseType::Int32:
        return 4;
        case BaseType::Int64:
        return 8;
        case BaseType::Float:
        return 8;
        case BaseType::Void:
        return 0;
    }
    return 0;
}

bool is_integral(BaseType base_type) {
    switch (base_type) {
        case BaseType::Int8:
        case BaseType::Int16:
        case BaseType::Int32:
        case BaseType::Int64:
        return true;
        default:
        return false;
    }
}

bool is_float(BaseType base_type) {
    return base_type == BaseType::Float;
}


enum class StorageType {
    Parameter, Local, Temp
};

struct VariableInfo {
    int64_t stack_offset;
    BaseType type_info;
    StorageType storage_type;
    size_t count;
    std::string variable_name;
};

struct SubroutineInfo {
    std::string subroutine_name;
    // total frame size (incl params size)
    size_t frame_size;
    // size of parameters
    size_t params_size;
    std::unordered_map<std::string, VariableInfo> variable_map;
};

struct Operand;

struct SubroutineRetInfo {
    uint64_t return_address;
    Operand* return_store;
    SubroutineInfo* return_sub;
};

struct CpuContext {
    uint64_t program_counter;
   
   //http://www.unixwiz.net/techtips/x86-jumps.html
   
    bool compare_equal; // = true of r0 - r1 is == 0, otherwise false
    bool compare_overflow; // = true if r0 - r1 overflows
    bool compare_sign; // = true if r0 - r1 is < 0 (Signed)

    ProgramStack stack;
    std::unordered_map<std::string, uint64_t> label_map;
    std::unordered_map<std::string, SubroutineInfo> subroutine_map;
    std::stack<SubroutineRetInfo> call_stack;
    SubroutineInfo* current_sub;
    uint64_t current_sub_base;
} ctx;

class Operand {
public:
    Operand(BaseType type) : type(type) {}

    template <typename T>
    void set(T t) {
        set_generic(static_cast<void*>(&t), std::min(base_type_size(type), sizeof(t)));
    }

    template <typename T>
    T get() {
        T t = {};
        memcpy(&t, get_generic(), std::min(base_type_size(type), sizeof(t)));
        return t;
    }
    
    BaseType get_type() {
        return type;
    }

    virtual void set_generic(void* value, size_t size) = 0;
    virtual void* get_generic() = 0;
    virtual ~Operand() {}

private:
    BaseType type;
};

class VarOperand : public Operand {
public:
    VarOperand(BaseType type, uint64_t var_stack_offset)
        : Operand(type), var_stack_offset(var_stack_offset) {}

    void set_generic(void* value, size_t size) override {
        const uint64_t frame_base = ctx.current_sub_base;
        ctx.stack.set_stack_var(frame_base + var_stack_offset, value, size);
    }
    
    void* get_generic() override {
        const uint64_t frame_base = ctx.current_sub_base;
        return ctx.stack.get_stack_var(frame_base + var_stack_offset);
    }
    virtual ~VarOperand() {}

private:
    uint64_t var_stack_offset;
};

class VarRefOperand : public Operand {
public:
    VarRefOperand(BaseType type, uint64_t var_stack_offset)
        : Operand(type), var_stack_offset(var_stack_offset) {}

    void set_generic(void* value, size_t size) override {
        throw std::runtime_error("Can't set a variable reference");
    }
    
    void* get_generic() override {
        var_net_offset = ctx.current_sub_base + var_stack_offset;
        return &var_net_offset;
    }

    virtual ~VarRefOperand() {}

private:
    uint64_t var_stack_offset;
    uint64_t var_net_offset;
};

class MemoryOperand : public Operand {
public:
    MemoryOperand(BaseType base_type, uint64_t var_stack_offset, int64_t offset, bool is_ref)
        : Operand(base_type), var_stack_offset(var_stack_offset), offset(offset), is_ref(is_ref) {}

    void set_generic(void* value, size_t size) override {
        const uint64_t frame_base = ctx.current_sub_base;
        if (is_ref) {
            int64_t stack_pointer = frame_base + var_stack_offset;
            ctx.stack.set_stack_var(stack_pointer + offset, value, size);
        } else {
            int64_t stack_pointer = *reinterpret_cast<int64_t*>(
                ctx.stack.get_stack_var(frame_base + var_stack_offset));
            ctx.stack.set_stack_var(stack_pointer + offset, value, size);
        }
    }
    
    void* get_generic() override {
        const uint64_t frame_base = ctx.current_sub_base;
        if (is_ref) {
            int64_t stack_pointer = frame_base + var_stack_offset;
            return ctx.stack.get_stack_var(stack_pointer + offset);
        } else {
            int64_t stack_pointer = *reinterpret_cast<int64_t*>(
                ctx.stack.get_stack_var(frame_base + var_stack_offset));
            return ctx.stack.get_stack_var(stack_pointer + offset);
        }
    }

    virtual ~MemoryOperand() {}

private:
    bool is_ref;
    uint64_t var_stack_offset;
    int64_t offset;
};

class LabelOperand : public Operand {
public:
    LabelOperand(std::string name) : Operand(BaseType::Int64), label_name(name) {}

    void set_generic(void* value, size_t size) override {
        throw std::runtime_error("Attempted set on LabelOperand");
    }

    void* get_generic() override {
        return &ctx.label_map[label_name];
    }

    const std::string get_name() {
        return label_name;
    }

    virtual ~LabelOperand() {}

private:
    std::string label_name;
};

class ImmediateOperand : public Operand {
public:
    ImmediateOperand(BaseType base_type, void* input_value) : Operand(base_type) {
        std::memcpy(static_cast<void*>(value), input_value, base_type_size(base_type));
    }

    void set_generic(void* value, size_t size) override {
        throw std::runtime_error("Attempted set on ImmediateOperand");
    }

    void* get_generic() override {
        return static_cast<void*>(value);
    }

    virtual ~ImmediateOperand() {}

private:
    uint8_t value[kPrimitiveMaxSize];
};

class Instruction {
public:
    Instruction(std::vector<Operand*> ops, BaseType op_cast = BaseType::Void) : op_cast(op_cast), operands(ops) {}

    virtual void execute(CpuContext& ctx) = 0;

    virtual ~Instruction() {
        for (Operand* operand : operands) {
            delete operand;
        }
    }

protected:
    std::vector<Operand*> operands;
    BaseType op_cast;
};

class NopInstruction : public Instruction {
public:
    using Instruction::Instruction;

    void execute(CpuContext& ctx) override {}

    virtual ~NopInstruction() {}
};

class MovInstruction : public Instruction {
public:
    using Instruction::Instruction;

    void execute(CpuContext& ctx) override {
        auto dest = operands[0];
        auto src = operands[1];
        BaseType cast_type = dest->get_type();
        if (op_cast != BaseType::Void) {
            cast_type = op_cast;
        }
        switch (cast_type) {
            case BaseType::Float:
                dest->set<double>(src->get<double>());
                break;
            case BaseType::Int64:
                dest->set<int64_t>(src->get<int64_t>());
                break;
            case BaseType::Int32:
                dest->set<int32_t>(src->get<int32_t>());
                break;
            case BaseType::Int16:
                dest->set<int16_t>(src->get<int16_t>());
                break;
            case BaseType::Int8:
                dest->set<int8_t>(src->get<int8_t>());
                break;
            default:
                throw std::runtime_error("Unexpected cast_type in mov");
        }
    }

    virtual ~MovInstruction() {}
};

class AddInstruction : public Instruction {
public:
    using Instruction::Instruction;
    
    void execute(CpuContext& ctx) override {
        auto dest = operands[0];
        auto src1 = operands[1];
        auto src2 = operands[2];
        BaseType cast_type = dest->get_type();
        if (op_cast != BaseType::Void) {
            cast_type = op_cast;
        }
        if (is_integral(dest->get_type()) != is_integral(src1->get_type()) ||
           (is_integral(dest->get_type()) != is_integral(src2->get_type()))) {
            throw std::runtime_error("Add called with mismatched types");
        }
        switch (cast_type) {
            case BaseType::Float:
                dest->set<double>(src1->get<double>() + src2->get<double>());
                break;
            case BaseType::Int64:
                dest->set<int64_t>(src1->get<int64_t>() + src2->get<int64_t>());
                break;
            case BaseType::Int32:
                dest->set<int32_t>(src1->get<int32_t>() + src2->get<int32_t>());
                break;
            case BaseType::Int16:
                dest->set<int16_t>(src1->get<int16_t>() + src2->get<int16_t>());
                break;
            case BaseType::Int8:
                dest->set<uint64_t>(src1->get<int8_t>() + src2->get<int8_t>());
                break;
            default:
                throw std::runtime_error("Unexpected cast_type in add");
        }
    }

    virtual ~AddInstruction() {}
};

class SubInstruction : public Instruction {
public:
    using Instruction::Instruction;

    void execute(CpuContext& ctx) override {
        auto dest = operands[0];
        auto src1 = operands[1];
        auto src2 = operands[2];
        BaseType cast_type = dest->get_type();
        if (op_cast != BaseType::Void) {
            cast_type = op_cast;
        }
        if (is_integral(dest->get_type()) != is_integral(src1->get_type()) ||
           (is_integral(dest->get_type()) != is_integral(src2->get_type()))) {
            throw std::runtime_error("Sub called with mismatched types");
        }
        switch (cast_type) {
            case BaseType::Float:
                dest->set<double>(src1->get<double>() - src2->get<double>());
                break;
            case BaseType::Int64:
                dest->set<int64_t>(src1->get<int64_t>() - src2->get<int64_t>());
                break;
            case BaseType::Int32:
                dest->set<int32_t>(src1->get<int32_t>() - src2->get<int32_t>());
                break;
            case BaseType::Int16:
                dest->set<int16_t>(src1->get<int16_t>() - src2->get<int16_t>());
                break;
            case BaseType::Int8:
                dest->set<uint64_t>(src1->get<int8_t>() - src2->get<int8_t>());
                break;
            default:
                throw std::runtime_error("Unexpected cast_type in sub");
        }
    }

    virtual ~SubInstruction() {}
};

class MulInstruction : public Instruction {
public:
    using Instruction::Instruction;

    void execute(CpuContext& ctx) override {
        auto dest = operands[0];
        auto src1 = operands[1];
        auto src2 = operands[2];
        BaseType cast_type = dest->get_type();
        if (op_cast != BaseType::Void) {
            cast_type = op_cast;
        }
        if (is_integral(dest->get_type()) != is_integral(src1->get_type()) ||
           (is_integral(dest->get_type()) != is_integral(src2->get_type()))) {
            throw std::runtime_error("Mul called with mismatched types");
        }
        switch (cast_type) {
            case BaseType::Float:
                dest->set<double>(src1->get<double>() * src2->get<double>());
                break;
            case BaseType::Int64:
                dest->set<int64_t>(src1->get<int64_t>() * src2->get<int64_t>());
                break;
            case BaseType::Int32:
                dest->set<int32_t>(src1->get<int32_t>() * src2->get<int32_t>());
                break;
            case BaseType::Int16:
                dest->set<int16_t>(src1->get<int16_t>() * src2->get<int16_t>());
                break;
            case BaseType::Int8:
                dest->set<uint64_t>(src1->get<int8_t>() * src2->get<int8_t>());
                break;
            default:
                throw std::runtime_error("Unexpected cast_type in mul");
        }
    }

    virtual ~MulInstruction() {}
};

class DivInstruction : public Instruction {
public:
    using Instruction::Instruction;

    void execute(CpuContext& ctx) override {
        auto dest = operands[0];
        auto src1 = operands[1];
        auto src2 = operands[2];
        BaseType cast_type = dest->get_type();
        if (op_cast != BaseType::Void) {
            cast_type = op_cast;
        }
        if (is_integral(dest->get_type()) != is_integral(src1->get_type()) ||
           (is_integral(dest->get_type()) != is_integral(src2->get_type()))) {
            throw std::runtime_error("Div called with mismatched types");
        }
        switch (cast_type) {
            case BaseType::Float:
                dest->set<double>(src1->get<double>() / src2->get<double>());
                break;
            case BaseType::Int64:
                dest->set<int64_t>(src1->get<int64_t>() / src2->get<int64_t>());
                break;
            case BaseType::Int32:
                dest->set<int32_t>(src1->get<int32_t>() / src2->get<int32_t>());
                break;
            case BaseType::Int16:
                dest->set<int16_t>(src1->get<int16_t>() / src2->get<int16_t>());
                break;
            case BaseType::Int8:
                dest->set<uint64_t>(src1->get<int8_t>() / src2->get<int8_t>());
                break;
            default:
                throw std::runtime_error("Unexpected cast_type in div");
        }
    }

    virtual ~DivInstruction() {}
};

class ModInstruction : public Instruction {
public:
    using Instruction::Instruction;
    
    void execute(CpuContext& ctx) override {
        auto dest = operands[0];
        auto src1 = operands[1];
        auto src2 = operands[2];
        BaseType cast_type = dest->get_type();
        if (op_cast != BaseType::Void) {
            cast_type = op_cast;
        }
        if (is_integral(dest->get_type()) != is_integral(src1->get_type()) ||
           (is_integral(dest->get_type()) != is_integral(src2->get_type()))) {
            throw std::runtime_error("Mod called with mismatched types");
        }
        switch (cast_type) {
            case BaseType::Float:
                break;
            case BaseType::Int64:
                dest->set<int64_t>(src1->get<int64_t>() % src2->get<int64_t>());
                break;
            case BaseType::Int32:
                dest->set<int32_t>(src1->get<int32_t>() % src2->get<int32_t>());
                break;
            case BaseType::Int16:
                dest->set<int16_t>(src1->get<int16_t>() % src2->get<int16_t>());
                break;
            case BaseType::Int8:
                dest->set<uint64_t>(src1->get<int8_t>() % src2->get<int8_t>());
                break;
            default:
                throw std::runtime_error("Unexpected cast_type in mod");
        }
    }

    virtual ~ModInstruction() {}
};

class CmpInstruction : public Instruction {
public:
    using Instruction::Instruction;
    
    void execute(CpuContext& ctx) override {
        auto src1 = operands[0];
        auto src2 = operands[1];
        BaseType cast_type = src1->get_type();
        if (op_cast != BaseType::Void) {
            cast_type = op_cast;
        }
        if (!is_integral(src1->get_type()) || !is_integral(src2->get_type())) {
            throw std::runtime_error("Non-integral cmp not allowed");
        }
        switch (cast_type) {
            case BaseType::Int64: {
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
            case BaseType::Int32: {
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
            case BaseType::Int16: {
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
            case BaseType::Int8: {
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
            default:
                throw std::runtime_error("Unexpected cast_type in cmp");
        }
    }

    virtual ~CmpInstruction() {}
};

enum class JmpCondition {
    None, Eq, NotEq, Gt, Lt, Ge, Le
};

class JmpInstruction : public Instruction {
public:
    JmpInstruction(std::vector<Operand*> ops, JmpCondition condition = JmpCondition::None) : Instruction(ops), condition(condition) {}

    void execute(CpuContext& ctx) override {
        auto dest = operands[0];
        if (dest->get_type() != BaseType::Int64) {
            throw std::runtime_error("Jump destination operand was not of expected type");
        }
        switch (condition) {
        case JmpCondition::None:
            ctx.program_counter = dest->get<uint64_t>() - 1;
            break;
        case JmpCondition::Eq:
            if (ctx.compare_equal) {
                ctx.program_counter = dest->get<uint64_t>() - 1;
            }
            break;
        case JmpCondition::NotEq:
            if (!ctx.compare_equal) {
                ctx.program_counter = dest->get<uint64_t>() - 1;
            }
            break;
        case JmpCondition::Lt:
            if (ctx.compare_sign != ctx.compare_overflow) {
                ctx.program_counter = dest->get<uint64_t>() - 1;
            }
            break;
        case JmpCondition::Le:
            if (ctx.compare_equal || ctx.compare_sign != ctx.compare_overflow) {
                ctx.program_counter = dest->get<uint64_t>() - 1;
            }
            break;
        case JmpCondition::Ge:
            if (ctx.compare_sign == ctx.compare_overflow) {
                ctx.program_counter = dest->get<uint64_t>() - 1;
            }
            break;
        case JmpCondition::Gt:
            if (ctx.compare_equal && ctx.compare_sign == ctx.compare_overflow) {
                ctx.program_counter = dest->get<uint64_t>() - 1;
            }
            break;
        }
    }

    virtual ~JmpInstruction() {}

private:
    JmpCondition condition;
};

class ParamInstruction : public Instruction {
public:
    using Instruction::Instruction;
    
    void execute(CpuContext& ctx) override {
        auto dest = operands[0];
        switch (op_cast) {
            case BaseType::Float: {
                float val = dest->get<float>();
                ctx.stack.push_stack_var(&val, sizeof(val));
                break;
            }
            case BaseType::Int64: {
                int64_t val = dest->get<int64_t>();
                ctx.stack.push_stack_var(&val, sizeof(val));
                break;
            }
            case BaseType::Int32: {
                int32_t val = dest->get<int32_t>();
                ctx.stack.push_stack_var(&val, sizeof(val));
                break;
            }
            case BaseType::Int16: {
                int16_t val = dest->get<int16_t>();
                ctx.stack.push_stack_var(&val, sizeof(val));
                break;
            }
            case BaseType::Int8: {
                int8_t val = dest->get<int8_t>();
                ctx.stack.push_stack_var(&val, sizeof(val));
                break;
            }
            default:
                throw std::runtime_error("Unexpected op_cast in param");
        }
    }
    virtual ~ParamInstruction() {}
};

class CallInstruction : public Instruction {
public:
    using Instruction::Instruction;
    
    void execute(CpuContext& ctx) override {
        auto dest = reinterpret_cast<LabelOperand*>(operands[0]);
        auto it = ctx.subroutine_map.find(dest->get_name());
        if (it == ctx.subroutine_map.end()) {
            throw std::runtime_error("Invalid subroutine name \"" + dest->get_name() + "\"");
        }
        auto called_subroutine = &it->second;
        ctx.call_stack.push(SubroutineRetInfo {
            .return_address = ctx.program_counter + 1,
            .return_store = operands.size() > 1 ? operands[1] : nullptr,
            .return_sub = ctx.current_sub,
        });
        ctx.stack.change_size(called_subroutine->frame_size - called_subroutine->params_size);
        // Step forward sub base based on current function size
        ctx.current_sub_base += ctx.current_sub->frame_size;
        ctx.current_sub = called_subroutine;
        ctx.program_counter = dest->get<uint64_t>();
    }

    virtual ~CallInstruction() {}
};

class ReturnInstruction : public Instruction {
public:
    using Instruction::Instruction;

    void execute(CpuContext& ctx) override {
        auto ret_info = ctx.call_stack.top();
        ctx.call_stack.pop();
        uint8_t value[kPrimitiveMaxSize];
        if (operands.size() > 0 && ret_info.return_store != nullptr) {
            auto ret_value = operands[0];
            memcpy(value, ret_value->get_generic(), base_type_size(ret_value->get_type()));
        }
        ctx.stack.change_size(-ctx.current_sub->frame_size);
        ctx.current_sub = ret_info.return_sub;
        // Step back based on calling sub's frame size
        ctx.current_sub_base -= ctx.current_sub->frame_size;
        if (operands.size() > 0 && ret_info.return_store != nullptr) {
            auto ret_value = operands[0];
            ret_info.return_store->set_generic(value, base_type_size(ret_value->get_type()));
        }
        ctx.program_counter = ret_info.return_address;
    }

    virtual ~ReturnInstruction() {}
};

class ArrayCopyInstruction : public Instruction {
public:
    ArrayCopyInstruction(size_t count, std::vector<Operand*> ops, BaseType op_cast = BaseType::Void)
        : copy_count(count), Instruction(ops, op_cast) {}

    void execute(CpuContext& ctx) override {
        auto dest = operands[0];
        auto src = operands[1];
        if (src->get_type() != BaseType::Int64 ||
            dest->get_type() != BaseType::Int64) {
            throw std::runtime_error("arraycopy called with non-pointer operands");
        }
        void* read_base = ctx.stack.get_stack_var(src->get<int64_t>());
        uint64_t write_addr = dest->get<int64_t>();
        for (size_t i = 0; i < copy_count; i++) {
            ctx.stack.set_stack_var(write_addr + i, read_base, 1);
        }
    }

    virtual ~ArrayCopyInstruction() {}

private:
    size_t copy_count;
};

class IntToFloatInstruction : public Instruction {
public:
    using Instruction::Instruction;

    void execute(CpuContext& ctx) override {
        auto dest = operands[0];
        auto src = operands[1];
        if (dest->get_type() != BaseType::Float) {
            throw std::runtime_error("IntToFloatInstruction destination was not of type float");
        }
        switch (src->get_type()) {
            case BaseType::Float:
                throw std::runtime_error("IntToFloatInstruction source was of type float");
            case BaseType::Int64:
                dest->set<double>(src->get<int64_t>());
                break;
            case BaseType::Int32:
                dest->set<double>(src->get<int32_t>());
                break;
            case BaseType::Int16:
                dest->set<double>(src->get<int16_t>());
                break;
            case BaseType::Int8:
                dest->set<double>(src->get<int8_t>());
                break;
            default:
                throw std::runtime_error("Unexpected cast_type in inttofloat");
        }
    }

    virtual ~IntToFloatInstruction() {}
};

class FloatToIntInstruction : public Instruction {
public:
    using Instruction::Instruction;

    void execute(CpuContext& ctx) override {
        auto dest = operands[0];
        auto src = operands[1];
        if (src->get_type() != BaseType::Float) {
            throw std::runtime_error("FloatToIntInstruction source was not of type float");
        }
        switch (dest->get_type()) {
            case BaseType::Float:
                throw std::runtime_error("FloatToIntInstruction dest was of type float");
            case BaseType::Int64:
                dest->set<int64_t>(src->get<float>());
                break;
            case BaseType::Int32:
                dest->set<int32_t>(src->get<float>());
                break;
            case BaseType::Int16:
                dest->set<int16_t>(src->get<float>());
                break;
            case BaseType::Int8:
                dest->set<int8_t>(src->get<float>());
                break;
            default:
                throw std::runtime_error("Unexpected cast_type in floattoint");
        }
    }

    virtual ~FloatToIntInstruction() {}
};

class PrintInstruction : public Instruction {
public:
    using Instruction::Instruction;

    void execute(CpuContext& ctx) override {
        auto src = operands[0];
        switch (src->get_type()) {
            case BaseType::Float:
                std::cout << src->get<float>() << std::endl;
                break;
            case BaseType::Int64:
                std::cout << src->get<int64_t>() << std::endl;
                break;
            case BaseType::Int32:
                std::cout << static_cast<int32_t>(src->get<int32_t>()) << std::endl;
                break;
            case BaseType::Int16:
                std::cout << static_cast<int32_t>(src->get<int16_t>()) << std::endl;
                break;
            case BaseType::Int8:
                std::cout << static_cast<int32_t>(src->get<int8_t>()) << std::endl;
                break;
            default:
                throw std::runtime_error("Unexpected cast_type in print");
        }
    }

    virtual ~PrintInstruction() {}
};

Operand* parse_destop(std::string& op, SubroutineInfo const& current_sub) {
    std::regex memref_re("^\\[(&?)([a-zA-Z0-9_-]+)\\s*(?:([+-])\\s*([0-9]+))?\\]::"
                         "(int8|int16|int32|int64|float)\\s*(.*)$");
    std::regex varref_re("^([a-zA-Z_][a-zA-Z_0-9]*)\\s*(.*)$");
    std::smatch matches;
    Operand* ret;
    if (std::regex_match(op, matches, memref_re)) {
        std::string varname = matches[2];
        auto it = current_sub.variable_map.find(varname);
        if (it == current_sub.variable_map.end()) {
            return nullptr;
        }
        std::string offset_str = matches[4];
        int offset = strtol(offset_str.c_str(), nullptr, 10);
        if (matches[3] == "-") {
            offset = -offset;
        }
        BaseType cast_type = type_from_string(matches[5]);
        ret = new MemoryOperand(cast_type, it->second.stack_offset, offset, matches[1] == "&");
        op = matches[6];
    } else if (std::regex_match(op, matches, varref_re)) {
        std::string varname = matches[1];
        auto it = current_sub.variable_map.find(varname);
        if (it == current_sub.variable_map.end()) {
            return nullptr;
        }
        ret = new VarOperand(it->second.type_info, it->second.stack_offset);
        op = matches[2];
    } else {
        return nullptr;
    }
    return ret;
}

Operand* parse_srcop(std::string& op, SubroutineInfo const& current_sub) {
    Operand* ret = parse_destop(op, current_sub);
    if (ret != nullptr) {
        return ret;
    }
    std::regex imm_type_re("(.*)::(int8|int16|int32|int64|float|cstring)\\s*(.*)$");
    std::regex varref_ptr_re("&([a-zA-Z_][a-zA-Z_0-9]*)\\s*(.*)$");
    std::smatch matches;
    if (std::regex_match(op, matches, imm_type_re)) {
        std::string imm_type = matches[2];
        std::string constant_str = matches[1];
        op = matches[3]; 
        BaseType base_type = type_from_string(imm_type);
        matches = {};
        if (is_integral(base_type)) {
            std::regex imm_val_re("([+-]?)(\\d+)\\s*$");
            if (!std::regex_match(constant_str, matches, imm_val_re)) {
                return nullptr;
            }
            std::string integral_val = matches[2];
            int64_t val = strtoll(integral_val.c_str(), nullptr, 10);
            if (matches[1] == "-") {
                val = -val;
            }
            ret = new ImmediateOperand(base_type, &val);
        } else if (is_float(base_type)) {
            std::regex imm_val_re("([+-]?)(\\d+(?:\\.\\d*))\\s*$");
            if (!std::regex_match(constant_str, matches, imm_val_re)) {
                return nullptr;
            }
            std::string integral_val = matches[2];
            double val = std::stod(integral_val);
            if (matches[1] == "-") {
                val = -val;
            }
            ret = new ImmediateOperand(base_type, &val);
        } else {
            // TODO: GLOBALS FUCKER
        }
    } else if (std::regex_match(op, matches, varref_ptr_re)) {
        std::string varname = matches[1];
        auto it = current_sub.variable_map.find(varname);
        if (it == current_sub.variable_map.end()) {
            return nullptr;
        }
        ret = new VarRefOperand(it->second.type_info, it->second.stack_offset);
        op = matches[2];
    } else {
        return nullptr;
    }
    return ret;
}

Instruction* parse_mov(std::string const& args, SubroutineInfo const& current_sub) {
    std::string op = args;
    Operand* des = parse_destop(op, current_sub);
    Operand* srcop = parse_srcop(op, current_sub);
    if (des == nullptr || srcop == nullptr) {
        return nullptr;
    }
    return new MovInstruction({des, srcop});
}

Instruction* parse_add(std::string const& args, SubroutineInfo const& current_sub) {
    std::string op = args;
    Operand* des = parse_destop(op, current_sub);
    Operand* srcop = parse_srcop(op, current_sub);
    Operand* srcop2 = parse_srcop(op, current_sub);
    if (des == nullptr || srcop == nullptr || srcop2 == nullptr) {
        return nullptr;
    }
    return new AddInstruction({des, srcop, srcop2});
}

Instruction* parse_sub(std::string const& args, SubroutineInfo const& current_sub) {
    std::string op = args;
    Operand* des = parse_destop(op, current_sub);
    Operand* srcop = parse_srcop(op, current_sub);
    Operand* srcop2 = parse_srcop(op, current_sub);
    if (des == nullptr || srcop == nullptr || srcop2 == nullptr) {
        return nullptr;
    }
    return new SubInstruction({des, srcop, srcop2});
}

Instruction* parse_mul(std::string const& args, SubroutineInfo const& current_sub) {
    std::string op = args;
    Operand* des = parse_destop(op, current_sub);
    Operand* srcop = parse_srcop(op, current_sub);
    Operand* srcop2 = parse_srcop(op, current_sub);
    if (des == nullptr || srcop == nullptr || srcop2 == nullptr) {
        return nullptr;
    }
    return new MulInstruction({des, srcop, srcop2});
}

Instruction* parse_div(std::string const& args, SubroutineInfo const& current_sub) {
    std::string op = args;
    Operand* des = parse_destop(op, current_sub);
    Operand* srcop = parse_srcop(op, current_sub);
    Operand* srcop2 = parse_srcop(op, current_sub);
    if (des == nullptr || srcop == nullptr || srcop2 == nullptr) {
        return nullptr;
    }
    return new DivInstruction({des, srcop, srcop2});
}

Instruction* parse_mod(std::string const& args, SubroutineInfo const& current_sub) {
    std::string op = args;
    Operand* des = parse_destop(op, current_sub);
    Operand* srcop = parse_srcop(op, current_sub);
    Operand* srcop2 = parse_srcop(op, current_sub);
    if (des == nullptr || srcop == nullptr || srcop2 == nullptr) {
        return nullptr;
    }
    return new ModInstruction({des, srcop, srcop2});
}

Instruction* parse_cmp(std::string const& args, SubroutineInfo const& current_sub) {
    std::string op = args;
    Operand* srcop = parse_srcop(op, current_sub);
    Operand* srcop2 = parse_srcop(op, current_sub);
    if (srcop == nullptr || srcop2 == nullptr) {
        return nullptr;
    }
    return new CmpInstruction({srcop, srcop2});
}

Operand* parse_label(std::string& op) {
    std::regex label_re("^([a-zA-Z_][a-zA-Z_0-9]*)\\s*(.*)$");
    std::smatch matches;
    if (!std::regex_match(op, matches, label_re)) {
        return nullptr;
    }
    Operand* label = new LabelOperand(matches[1]);
    op = matches[2];
    return label;
}

Instruction* parse_jmp(std::string const& args, JmpCondition condition, SubroutineInfo const& current_sub) {
    std::string op = args;
    Operand* label = parse_label(op);
    if (label == nullptr) {
        return nullptr;
    }
    return new JmpInstruction({label}, condition);
}

Instruction* parse_call(std::string const& args, SubroutineInfo const& current_sub) {
    std::string op = args;
    Operand* label = parse_label(op);
    Operand* dest = parse_destop(op, current_sub);
    if (label == nullptr || dest == nullptr) {
        return nullptr;
    }
    return new CallInstruction({label, dest});
}

Instruction* parse_param(std::string const& args, SubroutineInfo const& current_sub) {
    std::string op = args;
    Operand* srcop = parse_srcop(op, current_sub);
    if (srcop == nullptr) {
        return nullptr;
    }
    std::regex re("^\\s*(int8|int16|int32|int64|float)\\s*$");
    std::smatch matches;
    if (!std::regex_match(op, matches, re)) {
        delete srcop;
        return nullptr;
    }
    BaseType type = type_from_string(matches[1]);
    return new ParamInstruction({srcop}, type);
}

Instruction* parse_return(std::string const& args, SubroutineInfo const& current_sub) {
    std::string op = args;
    std::regex empty_re("\\s*$");

    Operand* srcop = parse_srcop(op, current_sub);
    if (srcop == nullptr) {
        if (std::regex_match(args, empty_re)) {
            return new ReturnInstruction(std::vector<Operand*>{});
        } else {
            return nullptr;
        }
    }
    return new ReturnInstruction({srcop});
}

Instruction* parse_arraycopy(std::string const& args, SubroutineInfo const& current_sub) {
    std::string op = args;
    Operand* des = parse_destop(op, current_sub);
    Operand* srcop = parse_srcop(op, current_sub);
    int size = stoi(args);
    
    if (des == nullptr || srcop == nullptr) {
        return nullptr;
    }
    return new ArrayCopyInstruction(size, {des, srcop});
}

Instruction* parse_inttofloat(std::string const& args, SubroutineInfo const& current_sub) {
    std::string op = args;
    Operand* des = parse_destop(op, current_sub);
    Operand* srcop = parse_srcop(op, current_sub);

    if (des == nullptr || srcop == nullptr) {
        return nullptr;
    }
    return new IntToFloatInstruction({des, srcop});
}

Instruction* parse_floattoint(std::string const& args, SubroutineInfo const& current_sub) {
    std::string op = args;
    Operand* des = parse_destop(op, current_sub);
    Operand* srcop = parse_srcop(op, current_sub);

    if (des == nullptr || srcop == nullptr) {
        return nullptr;
    }
    return new FloatToIntInstruction({des, srcop});
}

Instruction* parse_print(std::string const& args, SubroutineInfo const& current_sub) {
    std::string op = args;
    Operand* srcop = parse_srcop(op, current_sub);

    if (srcop == nullptr) {
        return nullptr;
    }
    return new PrintInstruction({srcop});
}

Instruction* parse_instruction(std::string line, size_t instruction_address, SubroutineInfo const& current_sub) {
    Instruction* instr = nullptr;
    std::regex optype("^\\s*(mov|add|sub|mul|div|mod|cmp|jmp|je|jne|jgt|jlt|jge|jle|param|label|call|return|arraycopy|inttofloat|floattoint|print)\\s*(.*)$");
    std::smatch matches;
    if (!std::regex_match(line, matches, optype)) {
        return nullptr;
    }
    std::string name = matches[1];
    std::string rest = matches[2];
    if (name == "mov") {
        instr = parse_mov(rest, current_sub);
    } else if (name == "add") {
        instr = parse_add(rest, current_sub);
    } else if (name == "sub") {
        instr = parse_sub(rest, current_sub);
    } else if (name == "mul") {
        instr = parse_mul(rest, current_sub);
    } else if (name == "div") {
        instr = parse_div(rest, current_sub);
    } else if (name == "mod") {
        instr = parse_mod(rest, current_sub);
    } else if (name == "cmp") {
        instr = parse_cmp(rest, current_sub);
    } else if (name == "jmp") {
        instr = parse_jmp(rest, JmpCondition::None, current_sub);
    } else if (name == "je") {
        instr = parse_jmp(rest, JmpCondition::Eq, current_sub);
    } else if (name == "jne") {
        instr = parse_jmp(rest, JmpCondition::NotEq, current_sub);
    } else if (name == "jgt") {
        instr = parse_jmp(rest, JmpCondition::Gt, current_sub);
    } else if (name == "jlt") {
        instr = parse_jmp(rest, JmpCondition::Lt, current_sub);
    } else if (name == "jge") {
        instr = parse_jmp(rest, JmpCondition::Ge, current_sub);
    } else if (name == "jle") {
        instr = parse_jmp(rest, JmpCondition::Le, current_sub);
    } else if (name == "param") {
        instr = parse_param(rest, current_sub);
    } else if (name == "call") {
        instr = parse_call(rest, current_sub);
    } else if (name == "return") {
        instr = parse_return(rest, current_sub);
    } else if (name == "arraycopy") {
        instr = parse_arraycopy(rest, current_sub);
    } else if (name == "inttofloat") {
        instr = parse_inttofloat(rest, current_sub);
    } else if (name == "floattoint") {
        instr = parse_floattoint(rest, current_sub);
    } else if (name == "print") {
        instr = parse_print(rest, current_sub);
    }
    return instr;
}

std::optional<VariableInfo> parse_frame_variable(std::string line) {
    std::regex re("^\\s*(in|local|temp)\\s+([a-zA-Z_][a-zA-Z_0-9]*)\\s+"
                  "(int8|int16|int32|int64|float)(?:\\s+(\\d+))?\\s*$");
    std::smatch re_results;
    if (!std::regex_match(line, re_results, re)) {
        return std::nullopt;
    }

    VariableInfo vi;
    vi.stack_offset = 0;
    vi.count = 1;
    if (re_results[1] == "in") {
        vi.storage_type = StorageType::Parameter;
    } else if (re_results[1] == "local") {
        vi.storage_type = StorageType::Local;
    } else if (re_results[1] == "temp") {
        vi.storage_type = StorageType::Temp;
    }
    vi.variable_name = re_results[2];
    vi.type_info = type_from_string(re_results[3]);
    std::string arr_count = re_results[4];
    if (!arr_count.empty()) {
        if (vi.storage_type == StorageType::Parameter) {
            throw std::runtime_error("Parameters are not allowed to be arrays");
        }
        vi.count = strtoll(arr_count.c_str(), nullptr, 10);
    }

    return vi;
}

std::optional<std::unordered_map<std::string, VariableInfo>>
parse_frame_description(std::ifstream& file) {
    std::unordered_map<std::string, VariableInfo> map;
    std::string line;
    for (getline_trim(file, line);
         line != ".endframe";
         getline_trim(file, line)) {
        if (file.eof()) {
            throw std::runtime_error("Unexpected EOF in parse_frame_description");
        }
        if (line.empty()) {
            continue;
        }
        std::optional<VariableInfo> vi = parse_frame_variable(line);
        if (vi == std::nullopt) {
            return std::nullopt;
        }
        map[vi->variable_name] = *vi;
    }
    return map;
}

std::optional<SubroutineInfo> parse_subroutine(std::ifstream& file, std::vector<Instruction*>& program) {
    std::string line = "";
    while (line.empty()) {
        if (file.eof()) {
            return std::nullopt;
        }
        getline_trim(file, line);
    }

    std::regex re("^\\s*.sub\\s+([a-zA-Z_][a-zA-Z_0-9]*)\\s*$");
    std::smatch matches;
    if (!std::regex_match(line, matches, re)) {
        throw std::runtime_error("Unexpected line \"" + line + "\" when \".sub\" was expected");
    }

    SubroutineInfo si;
    si.subroutine_name = matches[1];
    si.frame_size = 0;
    si.params_size = 0;
    auto frame_vars = parse_frame_description(file);
    if (!frame_vars) {
        return std::nullopt;
    }
    uint64_t cur_stackoff = 0;
    // compute frame size, params size, and parameter stack offsets
    for (auto&& [k, var_info] : *frame_vars) {
        const size_t var_size = base_type_size(var_info.type_info) * var_info.count;
        si.frame_size += var_size;
        if (var_info.storage_type == StorageType::Parameter) {
            si.params_size += var_size;
            var_info.stack_offset = cur_stackoff;
            cur_stackoff += var_size;
        }
    }
    // compute stack offset for non-parameters
    for (auto&& [k, var_info] : *frame_vars) {
        if (var_info.storage_type != StorageType::Parameter) {
            const size_t var_size = base_type_size(var_info.type_info) * var_info.count;
            var_info.stack_offset = cur_stackoff;
            cur_stackoff += var_size;
        }
    }
    si.variable_map = std::move(*frame_vars);

    // parse instructions
    for (getline_trim(file, line);
        line.find(".endsub") == std::string::npos;
        getline_trim(file, line)) {
        if (file.eof()) {
            throw std::runtime_error("Unexpected EOF in parse_subroutine");
        }

        trim_whitespace(line);
        if (line.empty()) {
            continue;
        }
        std::regex label_re("^\\.label\\s+([a-zA-Z_][a-zA-Z_0-9]*)\\s*$");
        std::smatch match;
        if (std::regex_match(line, match, label_re)) {
            ctx.label_map[match[1]] = program.size();
        } else {
            Instruction* inst = parse_instruction(line, program.size(), si);
            if (inst == nullptr) {
                throw std::runtime_error("Failed to parse line: " + line);
            }
            program.push_back(inst);
        }
    }

    return si;
}

int main(int argc, char** argv) {
    if (argc != 2) {
        std::cerr << "Invalid arguments\nUsage: ./interp <asm file>\n";
        return 1;
    }

    std::ifstream asm_file;
    asm_file.open(argv[1]);
    if (!asm_file.is_open()) {
        std::cerr << "File \"" << argv[1] << "\" not found\n";
        return 1;
    }
    std::string line;
    std::vector<Instruction*> program;

    try {
        auto subroutine = parse_subroutine(asm_file, program);
        while (subroutine) {
            ctx.subroutine_map[subroutine->subroutine_name] = subroutine.value();
            subroutine = parse_subroutine(asm_file, program);
        }
        if (ctx.subroutine_map.find("main") == ctx.subroutine_map.end()) {
            throw std::runtime_error("Failed to find entrypoint, should be main");
        }

        ctx.current_sub_base = 8;
        VarOperand program_ret(BaseType::Int64, 0);
        SubroutineInfo main_call{
            .frame_size = 8,
            .params_size = 0,
        };
        ctx.stack.change_size(8);
        ctx.call_stack.push(SubroutineRetInfo {
            .return_address = program.size(),
            .return_store = &program_ret,
            .return_sub = &main_call,
        });
        asm_file.close();
        ctx.current_sub = &ctx.subroutine_map["main"];
        ctx.program_counter = ctx.label_map["main"];
        ctx.stack.change_size(ctx.current_sub->frame_size - ctx.current_sub->params_size);
        while (ctx.program_counter < program.size()) {
            program[ctx.program_counter]->execute(ctx);
            ctx.program_counter++;
        }
        std::cout << "Done, returned " << program_ret.get<int64_t>() << std::endl;
    } catch (std::runtime_error e) {
        std::cerr << "Failed. Reason: " << e.what() << std::endl;
        return 1;
    }
    return 0;
}
