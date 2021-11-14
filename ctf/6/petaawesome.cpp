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
/*
mov eax, 12345
mov ecx, 11
again:
  lea ebx, [ecx * 8 + 0xf00b42]
  xor eax, ebx
  mov edx, ecx
  and edx, 1
  test edx, edx
  jz lbl
    rol eax, cl
    jmp jumpout
  lbl:
    rol eax, 17
  jumpout:
  dec ecx
  test ecx, ecx
  jnz again
and eax, 0x55555555
 */    
    eax = 12345;
    ecx = 11;
    
    do
    {
        ebx = ecx * 8 + 0xf00b42;
        eax ^= ebx;
        edx = ecx;
        edx &= 1;
        if (edx != 0)
        {
            eax = rol(eax, cl);
            // rol eax, cl
        }
        else
        {
            eax = rol(eax, 17);
            // rol eax, 17
        }
        ecx--;
    } while (ecx != 0);
    
    eax &= 0x55555555;
    
    
    std::cout << eax << std::endl;

    return 0;
}
