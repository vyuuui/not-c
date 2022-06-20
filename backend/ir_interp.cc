#include <variant>
#include <cstdint>
#include <unordered_map>
#include <vector>
#include <string>

enum class VarType {
    Int8, Int16, Int32, Int64, Float
};

class Label {
    uint64_t location;
};

class Stack {

};

int64_t get_type_mask(VarType type) {
    switch (type) {
        case VarType::Int8:
            return 0xff;
            break;
        case VarType::Int16:
            return 0xffff;
            break;
        case VarType::Int32:
            return 0xffffffff;
            break;
        case VarType::Int64:
            return 0xffffffffffffffff;
            break;
        case VarType::Float:
            return 0xffffffffffffffff;
            break;
    }
    return 0;
}

// alloc t0 40
// [x + 4]

// t3 
// [12]

class ProgramStack {
public:
    template <typename T>
    T* get_stack_var(size_t byte_off) {
        return reinterpret_cast<T*>(frame_data.data() + byte_off);
    }
    template <typename T>
    void set_stack_var(size_t byte_off, T const& val) {
        *get_stack_var<T>(byte_off) = val;
    }
    void change_size(ssize_t change) {
        frame_data.resize(frame_data.size() + change);
    }

private:
    std::vector<uint8_t> frame_data;
};

class Context {
    uint64_t program_counter;

    ProgramStack stack;
    std::unordered_map<std::string, uint64_t> label_map;
} ctx;

class Var {
public:
    Var(uint64_t stack_offset, VarType type) : stack_offset(stack_offset), type(type) { }

    VarType get_type() {
        return type;
    }

    template <typename T>
    T get() {
        int64_t generic = ctx. & get_type_mask(type);
        return *reinterpret_cast<T*>(&generic);
    }

private:
    uint64_t stack_offset;
    VarType type;
};




class Instruction {
public:
    Instruction(std::vector<std::string> ops) : operands(ops) {}
    virtual void execute(Context& ctx) = 0;

protected:
    std::vector<std::string> operands;
};


// "<name> x  y [z]"

class MovInstruction : public Instruction {
public:
    using Instruction::Instruction;

    void execute(Context& ctx) override {
        
        auto dest = operands[0];
        auto src = operands[1];
        switch (src->get_type()) {
            case VarType::Float:
                dest->set<double>(src->get<double>());
                break;
            case VarType::Int64:
            case VarType::Int32:
            case VarType::Int16:
            case VarType::Int8:
                dest->set<int64_t>(src->get<int64_t>());
                break;
            break;
        }
    }
};
