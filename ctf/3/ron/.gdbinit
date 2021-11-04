# just press Ctrl+c
run
echo "@@@@ FIND RESULT @@@@"
find 0x8000000, 0x8026000, (char)0x55, (char)0x48, (char)0x89, (char)0xE5, (char)0x48, (char)0x81
# call (void)kp2hack()
