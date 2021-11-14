/*
mov eax, 1337
mov ebx, 31337
add eax, ebx
mov ecx, eax
imul ebx, ecx
xor eax, ebx

*/

#include <stdio.h>

int main()
{
    int eax, ebx, ecx;
    eax = 1337;
    ebx = 31337;
    eax += ebx;
    ecx = eax;
    ebx *= ecx;
    eax ^= ebx;
    
    printf("%d\n", eax);

    return 0;
}
