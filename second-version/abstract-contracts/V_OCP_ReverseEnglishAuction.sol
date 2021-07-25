import "../interfaces/I_OCP_ReverseAuction.sol" ;
import "../abstract-contracts/V_OCP_EnglishAuction.sol" ;
import "../abstract-contracts/V_OCP_ReverseAuction.sol" ;
import "../contracts/OCP_AuctionBidder.spp" ;

abstract contract V_OCP_ReverseEnglishAuction is
V_OCP_EnglishAuction, V_OCP_ReverseAuction, I_OCP_ReverseAuction {

  function _init_reverse_english_auction (
                                          string kind,
                                          uint256 owner_pubkey,
                                          address owner_address,
                                          address root_wallet,
                                          uint256 time_stop,
                                          uint128 price_start,
                                          uint8 bid_min_increment,
                                          uint256 time_delay,
                                          address owner_vault,
                                          uint128 bidder_vault_target
               ) public
  {
    _init_english_auction( kind + "reverse ",
                           owner_pubkey,
                           owner_address,
                           root_wallet,
                           0,
                           time_stop,
                           price_start,
                           bid_min_increment,
                           time_delay,
                           owner_vault
                   );
    _init_reverse_auction(  bidder_vault_target );
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

    if( now < g_time_stop 
        && amount < g_current_price -
        ( g_current_price * g_bid_min_increment / 100 ) ){
      _accept_bid( amount, bidder_wallet, bidder_pubkey, msg.sender );
      g_bid_sender_contract = msg.sender ;
    } else {
      OCP_AuctionBidder( msg.sender ).unbid();
    }
  }

  function _transfer_funds_to_owner() internal override
  {
    _reverse_transfer_funds_to_owner();
  }

  function _refund_previous_bidder() internal override 
  {
    _reverse_transfer_funds_to_owner();
  }

}
