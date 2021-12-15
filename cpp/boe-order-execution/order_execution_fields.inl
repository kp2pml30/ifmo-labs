// granst that fields are sorted by offset
//
#ifndef FIELD
#  error You need to define FIELD(field, decoder_suffix, offset, length)
#endif

// to hack template parser suffix
#define ORDER_EXECUTION_COMMA_TOKEN ,

FIELD(cl_ord_id, string, 18, 20)
FIELD(exec_id, base36, 38, 8)
FIELD(filled_volume, double<4>, 46, 4)
FIELD(price, double<8 ORDER_EXECUTION_COMMA_TOKEN 10000>, 50, 8)
FIELD(active_volume, double<4>, 58, 4)
FIELD(liquidity_indicator, LiquidityIndicator, 62, 1)
FIELD(symbol, string, 0, 0)
FIELD(last_mkt, string, 0, 0)
FIELD(fee_code, string, 0, 0)

#undef ORDER_EXECUTION_COMMA_TOKEN
#undef FIELD
