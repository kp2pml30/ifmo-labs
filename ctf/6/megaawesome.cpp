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
    std::cout << ul << " " << s << std::endl;
    return (ul >> s) | (ul << sizeof(UT) * 8 - s);
}

std::int64_t nullifyTop(std::int64_t x) { return x & 0xffffffff; }

int main()
{
    // std::vector<int> stack;
    std::int64_t rax, rbx, rcx;
    std::int32_t
        &eax = lodword(rax),
        &ebx = lodword(rbx),
        &ecx = lodword(rcx)
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
/*
mov rax, 0x93f3ffc2fbc7a1ce
mov rbx, 6368891006275312830
imul eax, ebx
xchg al, ah
mov ebx, ebx
lea ebx, [ebx + eax * 2]
mov ecx, eax
ror ebx, cl
xor bx, ax
and ebx, 0xffffff
mov rax, rbx
 */    
    rax = 0x93f3ffc2fbc7a1ce;
    rbx = 6368891006275312830;
    
    // eax *= ebx; // top bytes?
    rax = nullifyTop(eax * ebx);
    { rax = nullifyTop(rax); std::swap(al, ah); }
    rbx = ebx; // nullify bytes
    rbx = ebx + eax * 2;
    rcx = eax;
    ebx = ror(ebx, cl);
    { rbx = nullifyTop(rbx); bx = bx ^ ax; } // what with bitssssss
    rbx = ebx & 0xffffff;
    rax = rbx;
    
    
    std::cout << rax << std::endl;

    return 0;
}
