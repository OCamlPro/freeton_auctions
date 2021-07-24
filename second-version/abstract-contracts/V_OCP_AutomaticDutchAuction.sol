import "V_OCP_DutchAuction.sol";

abstract contract V_OCP_AutomaticDutchAuction is V_OCP_DutchAuction {

  uint256 constant MAXIMAL_DURATION = 365 * 24 * 3600 ; // one year

  uint128 g_price_delta; // The price decrement over time
  uint256 g_time_delta; // The time after which the time
  uint256 g_time_start; // The starting time

  function _init_automatic_dutch_auction (
                                       string kind ,
                                       uint256 owner_pubkey,
                                       address owner_address,
                                       address root_wallet,
                                       uint128 price_start,
                                       uint128 price_stop,
                                       uint256 time_start,
                                       uint128 price_delta,
                                       uint256 time_delta
                                       ) internal
  {
      require( time_delta > 0
               && time_start >= now
               && price_delta > 0
               , OCP_Constants.EXN_INVALID_ARGUMENT );
      uint256 duration = time_delta +
        ( price_start - price_stop )
        * time_delta / price_delta ;
      require ( duration <= MAXIMAL_DURATION, OCP_Constants.EXN_INVALID_DURATION );
      uint256 time_stop = time_start + duration ;
      _init_dutch_auction(
                          kind + "automatic ",
                          owner_pubkey,
                          owner_address,
                          root_wallet,
                          time_stop,
                          price_start,
                          price_stop
                          );
      g_price_delta = price_delta ;
      g_time_start = time_start ;
      g_time_delta = time_delta ;
    }

  function _current_price ()
    internal view override returns (uint128 current_price){
    uint128 price_change =
      uint128( g_price_delta * (now - g_time_start) / g_time_delta ) ;
    current_price = g_price_start - price_change ;
    if( g_price_stop > current_price ){
      current_price = g_price_stop ;
    }
  }

  function get() public view
    returns ( Auction a,
              uint128 price_start,
              uint128 price_stop,
              uint256 time_start,
              uint256 time_delta,
              uint128 current_price
              )
  {
    a = _get_auction() ;
    price_start = g_price_start ;
    price_stop = g_price_stop ;
    time_start = g_time_start ;
    time_delta = g_time_delta ;
    if( now < g_time_stop ) {
      current_price = _current_price();
    }
  }

}
