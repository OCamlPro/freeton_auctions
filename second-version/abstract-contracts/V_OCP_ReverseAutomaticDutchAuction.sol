import "V_OCP_ReverseAuction.sol";

abstract contract V_OCP_ReverseAutomaticDutchAuction
is V_OCP_ReverseAuction, I_OCP_ReverseAuction {

  uint128 g_price_stop; // The limit price

  uint256 constant MAXIMAL_DURATION = 365 * 24 * 3600 ; // one year

  uint128 g_price_delta; // The price decrement over time
  uint256 g_time_delta; // The time after which the time
  uint256 g_time_start; // The starting time

  function _init_reverse_automatic_dutch_auction(
                               string kind,
                               uint256 owner_pubkey,
                               address owner_address,
                               address root_wallet,
                               uint128 price_start,
                               uint128 price_stop,
                                 uint256 time_start,
                                 uint128 price_delta,
                                 uint256 time_delta,
                               address owner_vault,
                               uint128 bidder_vault_target
           ) internal
  {
      require( time_delta > 0
               && time_start >= now
               && price_delta > 0
               , OCP_Constants.EXN_INVALID_ARGUMENT );
      uint256 duration = time_delta +
        ( price_stop - price_start )
        * time_delta / price_delta ;
      require ( duration <= MAXIMAL_DURATION,
                OCP_Constants.EXN_INVALID_DURATION );
      uint256 time_stop = time_start + duration ;
      require(
              price_start < price_stop
              , OCP_Constants.EXN_INVALID_ARGUMENT );
      _init_auction (
                     kind + "reverse automatic dutch ",
                     owner_pubkey,
                     owner_address,
                     root_wallet,
                     time_stop,
                     price_start,
                     owner_vault
                   ) ;
      g_price_delta = price_delta ;
      g_time_start = time_start ;
      g_time_delta = time_delta ;
      g_price_stop = price_stop ;
      g_automatic_winner = true ;
      _init_reverse_auction( bidder_vault_target );
  }

  function _current_price ()
    internal view returns (uint128 current_price){
    uint128 price_change =
      uint128( g_price_delta * (now - g_time_start) / g_time_delta ) ;
    current_price = g_price_start + price_change ;
    if( g_price_stop < current_price ){
      current_price = g_price_stop ;
    }
  }

  function _is_better_price (uint128 b) internal view returns (bool){
    uint128 current_price = _current_price() ;
    return ( g_price_start <= b && b <= current_price ) ;
  }

  function bid( uint128 amount,
                address bidder_wallet,
                uint256 bidder_pubkey
                ) public override
  {
    require( msg.value > OCP_Constants.MINIMAL_FEE,
             OCP_Constants.EXN_NOT_ENOUGH_VALUE );
    require( g_bidder_code_hash == 0, OCP_Constants.EXN_AUTH_FAILED );

    address addr = _calcBidderAddress( bidder_wallet, bidder_pubkey );
    require( msg.sender.value != 0
             && addr == msg.sender, OCP_Constants.EXN_AUTH_FAILED );
    TvmCell empty ;
    if( now < g_time_stop && _is_better_price( amount ) ){
      g_time_stop = now ;
      g_winner_address = bidder_wallet ;
      g_winner_pubkey = bidder_pubkey ;
      g_bid_sender_wallet = bidder_wallet ;
      g_bid_sender_contract = msg.sender ;
      g_final_price = amount ;
      emit Winner( g_winner_address, g_winner_pubkey );
      _reverse_transfer_funds_to_owner();
    } else {
      OCP_AuctionBidder( msg.sender ).unbid();
    }
  }

}
