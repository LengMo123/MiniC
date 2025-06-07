Value *IntAST::codegen() {
    return ConstantFP::get(*TheContext, AP)
}