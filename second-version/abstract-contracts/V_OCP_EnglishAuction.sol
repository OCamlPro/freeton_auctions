import "V_OCP_Auction.sol" ;


abstract contract V_OCP_EnglishAuction is V_OCP_Auction {

  uint128 constant MINIMAL_FEE = 0.5 ton ;

  uint128 g_price_start ;
  uint8 g_bid_min_increment ;
  uint256 g_time_delay ;
  bool g_need_refund ;
  uint256 g_time_max ;
  uint128 g_current_price ;
  uint256 g_bid_sender_pubkey ;
  address g_bid_sender_address ;
  address g_bid_sender_wallet ;
  uint256 g_time_blind ;
  
  function _init_english_auction(
                               string kind,
                               uint256 owner_pubkey,
                               address owner_address,
                               address root_wallet,
                               uint256 time_blind,
                               uint256 time_stop,
                               uint128 price_start,
                               uint8 bid_min_increment,
                               uint256 time_delay,
                               address owner_vault
           ) internal
  {
    require( time_blind == 0
             || ( time_blind > now && time_blind < time_stop ),
             OCP_Constants.EXN_INVALID_ARGUMENT );
    _init_auction (
                   kind + "english ",
                   owner_pubkey,
                   owner_address,
                   root_wallet,
                   time_stop,
                   owner_vault
                   ) ;
    g_price_start = price_start ;
    g_time_delay = time_delay ;
    g_time_max = time_stop ;
    g_current_price = price_start ;
    g_bid_min_increment = bid_min_increment ;
    g_time_blind = time_blind ;
  }


  function transfer_funds_to_owner() internal virtual ;
  function refund_previous_bidder() internal virtual ;

  function commit() public
  {
    _only_after_close () ;
    require( g_need_refund || !g_automatic_winner,
             OCP_Constants.EXN_AUTH_FAILED );
    tvm.accept();

    if( g_need_refund ){
      g_need_refund = false ;
      g_owner_address = g_bid_sender_address ;
      g_owner_pubkey = g_bid_sender_pubkey ;
      transfer_funds_to_owner();
      if( g_root_wallet.value != 0 ){
        ITONTokenWallet( g_auction_wallet ).destroy ( g_owner_address );
      }
    } else {
      g_automatic_winner = true ;
    }
  }

  function _accept_bid(
                       uint128 proposed_price ,
                       address bid_sender_wallet ,
                       uint256 bid_sender_pubkey ,
                       address bid_sender_address
                       ) internal
  {
    if( g_need_refund ){
      refund_previous_bidder ( );
    }
    g_need_refund = true ;
    g_current_price = proposed_price ;
    g_bid_sender_address = bid_sender_address ;
    g_bid_sender_pubkey = bid_sender_pubkey ;
    g_bid_sender_wallet = bid_sender_wallet ;
    if( g_time_delay > 0 ){
      g_time_stop = now + g_time_delay ;
      if ( g_time_stop > g_time_max ){
        g_time_stop = g_time_max ;
      }
    }
  }

  function get() public view
    returns ( Auction a,
              uint128 price_start,
              uint8 bid_min_increment,
              uint256 time_delay
              )
  {
    a = _get_auction() ;
    price_start = g_price_start ;
    time_delay = g_time_delay ;
    bid_min_increment = g_bid_min_increment ;
  }
  
}
