
import "V_OCP_EnglishAuction.sol" ;

abstract contract V_OCP_DirectEnglishAuction is V_OCP_EnglishAuction {

  function send_collected_fund( address target ) internal view
  {
      if ( g_root_wallet.value == 0 ) {
        target.transfer( g_current_price, false, 0 );
      } else {
        TvmCell empty ;
        ITONTokenWallet( g_auction_wallet ).
          transfer (
                    target,
                    g_current_price,
                    OCP_Constants.TRANSFER_GRAMS,
                    address(this),
                    true,
                    empty
                    );
      }
  }

  function _transfer_funds_to_owner() internal override
  {
    send_collected_fund ( g_owner_address );
  }

  function _refund_previous_bidder() internal override
  {
    send_collected_fund ( g_bid_sender_wallet );
  }

  receive() external
  {
    if( now > g_time_stop ){

      require( msg.sender == g_winner_address
               || msg.sender == g_owner_address
               , OCP_Constants.EXN_AUCTION_CLOSED );
    } else {

      if( msg.sender != g_owner_address ){

        require( g_time_blind != 0, OCP_Constants.EXN_BLIND_AUCTION );
        require( g_root_wallet.value == 0, OCP_Constants.EXN_WRONG_TOKEN );
        require( msg.value > MINIMAL_FEE, OCP_Constants.EXN_NOT_ENOUGH_VALUE );
        uint128 proposed_price = msg.value - MINIMAL_FEE ;
        if( proposed_price >
            g_current_price + ( g_current_price * g_bid_min_increment / 100 )
            ){
          _accept_bid(
                      proposed_price ,
                      msg.sender ,
                      0 ,
                      msg.sender
                      );
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
    if( amount > g_current_price ){

      _accept_bid(
                  amount ,
                  sender_wallet ,
                  sender_public_key ,
                  sender_address
                  ) ;

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


