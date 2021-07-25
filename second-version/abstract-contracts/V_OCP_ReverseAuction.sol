import "../interfaces/I_OCP_ReverseAuction.sol" ;
import "../abstract-contracts/V_OCP_Auction.sol" ;
import "../contracts/OCP_AuctionBidder.spp" ;

abstract contract V_OCP_ReverseAuction is
/*I_OCP_ReverseAuction, */ V_OCP_Auction {

  uint256 constant OCP_AuctionBidder_CODEHASH =
    0x%{get-code-hash:contract:tvc:OCP_AuctionBidder};
  
  uint128 g_auction_wallet_balance ;
  address g_bid_sender_contract ;
  uint256 g_bidder_code_hash;
  uint128 g_bidder_vault_target ;

  TvmCell g_bidder_code ;

  function _init_reverse_auction (
                                  uint128 bidder_vault_target
                                  ) public
  {
    g_bidder_code_hash = OCP_AuctionBidder_CODEHASH ;
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

  function _reverse_transfer_funds_to_owner() internal  view
  {
    TvmCell empty;
    OCP_AuctionBidder( g_bid_sender_contract ).
      winner( g_owner_vault );
    if( g_root_wallet.value != 0 ){
      ITONTokenWallet( g_auction_wallet ).
        transfer(
                 g_bid_sender_wallet,
                 g_final_price,
                 OCP_Constants.TRANSFER_GRAMS,
                 address(this),
                 true,
                 empty
                 );
      ITONTokenWallet( g_auction_wallet ).
        transfer(
                 g_owner_address,
                 g_auction_wallet_balance - g_final_price,
                 OCP_Constants.TRANSFER_GRAMS,
               address(this),
                 true,
                 empty
                 );
    } else {
      g_bid_sender_wallet.transfer( g_final_price, false, 0 );
      g_owner_address.transfer( g_auction_wallet_balance - g_final_price,
                                false, 0 );
    }
  }

  function _reverse_refund_previous_bidder() internal view
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

  receive() external
    {
      if( g_root_wallet.value != 0 ){
        g_auction_wallet_balance += msg.value;
      }
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

  function create_bidder( address bidder_wallet ) public view
    responsible returns ( address addr )
  {
    require( g_auction_wallet_balance >= g_price_start,
             OCP_Constants.EXN_NOT_READY );
    require( msg.value > OCP_Constants.MINIMAL_INITIAL_BALANCE );
    addr = new OCP_AuctionBidder
      {
      value: OCP_Constants.MINIMAL_INITIAL_BALANCE ,
      varInit: {
        s_bidder_wallet: bidder_wallet,
        s_auction : address(this)
      },
      pubkey: msg.pubkey(),
      code: g_bidder_code
      } ( g_root_vault, g_bidder_vault_target );
  }

}
