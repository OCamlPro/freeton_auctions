import "../interfaces/I_OCP_ReverseAuction.sol" ;
import "../abstract-contracts/V_OCP_EnglishAuction.sol" ;
import "../contracts/OCP_AuctionBidder.spp" ;

abstract contract V_OCP_ReverseEnglishAuction is
         I_OCP_ReverseAuction, V_OCP_EnglishAuction {

  uint128 g_auction_wallet_balance ;
  address g_bid_sender_contract ;
  uint256 g_bidder_code_hash;
  uint128 g_bidder_vault_target ;

  TvmCell g_bidder_code ;

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
                                          uint128 bidder_vault_target,
                                          uint256 bidder_code_hash
               ) public
  {
    require( bidder_code_hash != 0, OCP_Constants.EXN_INVALID_ARGUMENT );
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
    g_bidder_code_hash = bidder_code_hash ;
    g_bidder_vault_target = bidder_vault_target ;
  }

  function set_bidder_code( TvmCell code ) public
  {
    require( g_bidder_code_hash != 0, OCP_Constants.EXN_INVALID_ARGUMENT );
    require( tvm.hash(code) == g_bidder_code_hash,
             OCP_Constants.EXN_INVALID_ARGUMENT );
    tvm.accept();
    g_bidder_code = code ;
    g_bidder_code_hash = 0 ;
  }

  function transfer_funds_to_owner() internal override
  {
    TvmCell empty;
    OCP_AuctionBidder( g_bid_sender_contract ).
      transfer( g_owner_vault );
    ITONTokenWallet( g_auction_wallet ).
      transfer(
               g_bid_sender_wallet,
               g_current_price,
               OCP_Constants.TRANSFER_GRAMS,
               address(this),
               true,
               empty
               );
    ITONTokenWallet( g_auction_wallet ).
      transfer(
               g_owner_address,
               g_auction_wallet_balance - g_current_price,
               OCP_Constants.TRANSFER_GRAMS,
               address(this),
               true,
               empty
               );
  }

  function refund_previous_bidder() internal override
  {
    OCP_AuctionBidder( g_bid_sender_contract ).unbid();
  }

  function _tokens_received( uint128 amount,
                             address /*sender_wallet*/,
                             uint256 /*sender_public_key*/,
                             address /*sender_address*/ ) internal override
  {
    g_auction_wallet_balance += amount ;
  }

  function _calcBidderAddress(
                              address bidder_wallet,
                              uint256 bidder_pubkey
                              ) internal view returns (address addr)
  {
    TvmCell stateInit = tvm.buildStateInit({
        contr: OCP_AuctionBidder,
      varInit: {
        s_bidder_wallet: bidder_wallet,
        s_auction : address(this)
            },
          pubkey: bidder_pubkey,
          code: g_bidder_code
        });

    addr = address( tvm.hash( stateInit ) );
  }

  function bid( uint128 amount,
                address bidder_wallet,
                uint256 bidder_pubkey,
                address bidder_vault ) public override
  {
    require( msg.value > OCP_Constants.MINIMAL_FEE, OCP_Constants.EXN_NOT_ENOUGH_VALUE );
    require( g_bidder_code_hash == 0, OCP_Constants.EXN_AUTH_FAILED );

    address addr = _calcBidderAddress( bidder_wallet, bidder_pubkey );
    require( msg.sender.value != 0
             && addr == msg.sender, OCP_Constants.EXN_AUTH_FAILED );

    if( now < g_time_stop 
        && amount < g_current_price -
        ( g_current_price * g_bid_min_increment / 100 ) ){
      _accept_bid( amount, bidder_wallet, bidder_pubkey, bidder_vault );
      g_bid_sender_contract = msg.sender ;
    } else {
      OCP_AuctionBidder( msg.sender ).unbid();
    }
  }

}
