
library OCP_Constants {

  uint8 constant EXN_AUTH_FAILED         = 100 ;
  uint8 constant EXN_INVALID_ARGUMENT    = 101 ;
  uint8 constant EXN_WRONG_TOKEN         = 102 ;
  uint8 constant EXN_AUCTION_CLOSED      = 103 ;
  uint8 constant EXN_NOT_ENOUGH_VALUE    = 104 ;
  uint8 constant EXN_AUCTION_NOT_CLOSED  = 105 ;
  uint8 constant EXN_ALREADY_INITIALIZED = 106 ;
  uint8 constant EXN_INVALID_DURATION    = 107 ;
  uint8 constant EXN_NOT_ENOUGH_BALANCE  = 108 ;
  uint8 constant EXN_ALREADY_BIDDING     = 109 ;
  uint8 constant EXN_BLIND_AUCTION       = 110 ;
  uint8 constant EXN_NOT_READY           = 111 ;
  
  uint128 constant MINIMAL_INITIAL_BALANCE = 1 ton ;
  uint128 constant DEPLOY_WALLET_GRAMS = 0.5 ton ;
  uint128 constant QUERY_ADDRESS_GRAMS = 0.1 ton ;
  uint128 constant TRANSFER_GRAMS = 0.1 ton ;
  uint128 constant MINIMAL_FEE = 0.5 ton ;

}
