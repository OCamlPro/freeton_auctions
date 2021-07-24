import "V_OCP_Auction.sol";

abstract contract V_OCP_DutchAuction is V_OCP_Auction {

  uint128 g_price_start; // The starting price
  uint128 g_price_stop; // The limit price

  function _init_dutch_auction(
                               string kind,
                               uint256 owner_pubkey,
                               address owner_address,
                               address root_wallet,
                               uint256 time_stop,
                               uint128 price_start,
                               uint128 price_stop
           ) internal
  {
    require(
            price_start > price_stop
            , OCP_Constants.EXN_INVALID_ARGUMENT );
    _init_auction (
                   kind + "dutch ",
                   owner_pubkey,
                   owner_address,
                   root_wallet,
                   time_stop,
                   address(0)
                   ) ;
    g_price_start = price_start ;
    g_price_stop = price_stop ;
    g_automatic_winner = true ;
  }

  function _current_price () internal view virtual
    returns (uint128 current_price) ;

  function _is_better_price (uint128 b) internal view returns (bool){
    uint128 current_price = _current_price() ;
    return ( g_price_start >= b && b >= current_price ) ;
  }

  receive() external
  {
    if( now > g_time_stop ){

      require( msg.sender == g_winner_address
               || msg.sender == g_owner_address
               , OCP_Constants.EXN_AUCTION_CLOSED );

    } else {

      if( msg.sender != g_owner_address ){

        require( g_root_wallet.value == 0, OCP_Constants.EXN_WRONG_TOKEN );
        require( msg.value > OCP_Constants.MINIMAL_FEE, OCP_Constants.EXN_NOT_ENOUGH_VALUE );
        uint128 proposed_price = msg.value - OCP_Constants.MINIMAL_FEE ;
        if( _is_better_price ( proposed_price  ) ){
          g_time_stop = now ;
          g_winner_address = msg.sender ;

          emit Winner( g_winner_address, g_winner_pubkey );
          g_owner_address.transfer(
                                   proposed_price +
                                   ( address(this).balance - msg.value )
                                   , false, 0 );
        } else {
          msg.sender.transfer(0, false, 64);
        }
      }
    }
  }

  function _tokens_received( uint128 amount,
                             address sender_wallet,
                             uint256 sender_public_key,
                             address sender_address ) internal override
  {
    _only_before_close () ;
    TvmCell empty ;
    if( _is_better_price( amount ) ){
      g_time_stop = now ;
      g_winner_address = sender_address ;
      g_winner_pubkey = sender_public_key ;
      emit Winner( g_winner_address, g_winner_pubkey );

      ITONTokenWallet( g_auction_wallet ).
        transfer (
                  g_owner_address,
                  amount,
                  OCP_Constants.TRANSFER_GRAMS,
                  address(this),
                  true,
                  empty
                  );
      ITONTokenWallet( g_auction_wallet ).destroy ( g_owner_address );
    } else {

      ITONTokenWallet( g_auction_wallet ).
        transfer (
                  sender_wallet,
                  amount,
                  OCP_Constants.TRANSFER_GRAMS,
                  address(this),
                  true,
                  empty
                  );
      
    }
  }

}
