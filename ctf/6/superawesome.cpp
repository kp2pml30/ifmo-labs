/*
mov eax, 0x11223344
mov ebx, 3344556677
push eax
not eax
xor eax, ebx
mov bl, al
push ebx
shr ebx, 16
xor ebx, eax
pop eax
shr eax, 8
add eax, ebx
pop ebx
sub eax, ebx

 */

#include <iostream>
#include <cstdint>

std::int8_t& lobyte(auto &a) { return reinterpret_cast<std::int8_t&>(a); }
std::int16_t& loword(auto &a) { return reinterpret_cast<std::int16_t&>(a); }

int main()
{
    // std::vector<int> stack;
    int eax, ebx, ecx;
    eax = 0x11223344;
    ebx = 3344556677;
    // push 0x11223344
    eax = ~eax;
    eax ^= ebx;
    lobyte(ebx) = lobyte(eax);
    {
        const int pushEbx = ebx;
        ebx >>= 16;
        ebx ^= eax;
        eax = pushEbx;
    }
    eax >>= 8;
    eax += ebx;
    ebx = 0x11223344;
    eax -= ebx;
    
    std::cout << loword(eax) << std::endl;

    return 0;
}
