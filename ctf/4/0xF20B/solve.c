/******************************************************************************

                            Online C Compiler.
                Code, Compile, Run and Debug C program online.
Write your code in this editor and press "Run" button to compile and execute it.

*******************************************************************************/

#include <stdio.h>

int main()
{
  char key[40];
  memcpy(key, "]B", 2);
  key[2] = 30;
  key[3] = 29;
  key[4] = 117;
  key[5] = 94;
  key[6] = 66;
  key[7] = 25;
  key[8] = 117;
  key[9] = 98;
  key[10] = 25;
  key[11] = 102;
  key[12] = 102;
  key[13] = 117;
  key[14] = 67;
  key[15] = 89;
  key[16] = 117;
  key[17] = 108;
  key[18] = 120;
  key[19] = 26;
  strcpy(&key[20], "hd\x1Bik~o");
  memfrob(key, sizeof(key) - 5);
  printf("%s\n", key);
  return 0;
}
