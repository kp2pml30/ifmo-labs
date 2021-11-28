#include <iostream>
#include <cstdint>
#include <type_traits>

std::int8_t& lobyte(auto &a) { return reinterpret_cast<std::int8_t&>(a); }
std::int16_t& loword(auto &a) { return reinterpret_cast<std::int16_t&>(a); }
std::int32_t& lodword(auto &a) { return reinterpret_cast<std::int32_t&>(a); }

template<typename T>
T ror(T l, int s)
{
    if (s < 0) abort();
    s %= 32;
    using UT = std::make_unsigned_t<T>;
    auto const ul = UT(l);
    // std::cout << ul << " " << s << std::endl;
    return (ul >> s) | (ul << sizeof(UT) * 8 - s);
}

template<typename T>
T rol(T l, int s)
{
    if (s < 0) abort();
    s %= 32;
    using UT = std::make_unsigned_t<T>;
    auto const ul = UT(l);
    // std::cout << ul << " " << s << std::endl;
    return (ul << s) | (ul >> sizeof(UT) * 8 - s);
}

std::int64_t nullifyTop(std::int64_t x) { return x & 0xffffffff; }

int main()
{
    // std::vector<int> stack;
    std::int64_t rax, rbx, rcx, rdx;
    std::int32_t
        &eax = lodword(rax),
        &ebx = lodword(rbx),
        &ecx = lodword(rcx),
        &edx = lodword(rdx)
        ;
    std::int16_t
        &ax = loword(rax),
        &bx = loword(rbx),
        &cx = loword(rcx)
        ;
    std::int8_t
        &al = lobyte(eax),
        &cl = lobyte(ecx),
        &ah = *(reinterpret_cast<std::int8_t*>(&rax) + 1)
        ;

    eax = -237489155;
    
    
    eax ^= 0x64198234;
    eax = rol(eax, 14);
    
    
    std::cout << eax << std::endl;
    printf("%4s", &eax); // perl

    return 0;
}
