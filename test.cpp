#include <iostream>
#include <typeinfo>
#include <vector>

int main() {
    float n = 1.0;
    bool m = true;
    float result = n + m;
    std::vector<std::string> I;
    I.push_back("MOG");
    I.push_back("asdjhioasd");
    fprintf(stderr, I.back().c_str());
    return 1;
}