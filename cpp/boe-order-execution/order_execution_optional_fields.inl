// granst that fields are sorted by offset -> mask

#ifndef OPTIONAL_FIELD
# error You need to define OPTIONAL_FIELD(field, decoder_suffix, offset, mask, length)
#endif

#define ORDER_EXECUTION_COMMA_TOKEN ,

OPTIONAL_FIELD(symbol, string, 2, 1, 8)
OPTIONAL_FIELD(last_mkt, string, 7, 128, 4)
OPTIONAL_FIELD(fee_code, string, 8, 1, 2)

#undef ORDER_EXECUTION_COMMA_TOKEN
#  undef OPTIONAL_FIELD
