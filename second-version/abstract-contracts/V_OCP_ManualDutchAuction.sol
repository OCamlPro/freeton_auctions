import "V_OCP_DutchAuction.sol" ;

abstract contract V_OCP_ManualDutchAuction is V_OCP_DutchAuction {

  event NewPrice( uint128 new_price );

  uint256 g_auction_house_pubkey ;
  address g_auction_house_address ;
  uint128 g_current_price ;

  function _init_manual_dutch_auction (
                                       string kind,
                                       uint256 owner_pubkey,
                                       address owner_address,
                                       address root_wallet,
                                       uint256 time_stop,
                                       uint128 price_start,
                                       uint128 price_stop,
                                       uint256 auction_house_pubkey,
                                       address auction_house_address
               ) public
         {
           require( time_stop > now
                    , OCP_Constants.EXN_INVALID_ARGUMENT );
           _init_dutch_auction(
                               kind + "manual ",
                               owner_pubkey,
                               owner_address,
                               root_wallet,
                               time_stop,
                               price_start,
                               price_stop
                               );
           g_current_price = price_start ;
           g_auction_house_address = auction_house_address ;
           g_auction_house_pubkey = auction_house_pubkey ;
         }


  function _only_owner_or_auction_house( ) internal view returns (bool)
  {
    return
      ( g_winner_address.value != 0 &&
        msg.sender == g_winner_address )
      ||
      ( g_winner_pubkey != 0 &&
        msg.pubkey() == g_winner_pubkey ) ;
  }

  function _current_price ()
    internal view override returns (uint128 price){
    price = g_current_price ;
  }

  function update_price( uint128 new_price ) public
  {
    _only_before_close () ;

    if( g_auction_house_pubkey != 0 ||
        g_auction_house_address.value != 0 ){
      require(
              ( msg.pubkey() == 0 )
              ? ( g_auction_house_address.value != 0
                  && msg.sender == g_auction_house_address )
              : ( g_auction_house_pubkey != 0
                  && msg.pubkey() == g_auction_house_pubkey )
              , OCP_Constants.EXN_AUTH_FAILED );
    } else {
      _only_owner () ;
    }
    require(
            g_current_price >= new_price
            && new_price >= g_price_stop 
            , OCP_Constants.EXN_INVALID_ARGUMENT );
    tvm.accept();
    g_current_price = new_price ;
    emit NewPrice( new_price );
  }

  function get() public view
    returns ( Auction a,
              uint128 price_start,
              uint128 price_stop,
              uint256 auction_house_pubkey,
              address auction_house_address,
              uint128 current_price
              )
  {
    a = _get_auction() ;
    price_start = g_price_start ;
    price_stop = g_price_stop ;
    auction_house_address = g_auction_house_address ;
    auction_house_pubkey = g_auction_house_pubkey ;
    if( now < g_time_stop ) {
      current_price = _current_price();
    }
  }

}
