import "../libraries/OCP_Constants.sol" ;
import "../external-interfaces/ITONTokenWallet.sol" ;
import "../external-interfaces/ITokensReceivedCallback.sol" ;
import "../external-interfaces/IRootTokenContract.sol" ;


abstract contract V_OCP_Auction is ITokensReceivedCallback {

  event Winner( address g_winner_address, uint256 g_winner_pubkey );

  struct Auction {
    uint256 id ;
    address initial_owner_address ;
    address owner_address ;
    uint256 owner_pubkey ;
    uint256 time_stop ;
    address root_wallet ;
    address auction_wallet ;
    bool reverse ;
    address root_vault ;
    address owner_vault;
    address winner_address ;
    uint256 winner_pubkey ;
    string kind ;
    string title ;
    string description ;
  }

  uint256 static s_id ;
  address static s_owner_address ;

  address g_owner_address ;
  uint256 g_owner_pubkey ;

  uint256 g_time_stop;
  address g_root_wallet ;
  address g_auction_wallet ;
  
  address g_winner_address ;
  uint256 g_winner_pubkey ;

  bool g_automatic_winner ;
  string g_kind ;
  string g_title ;
  string g_description ;

  // reverse auctions
  bool g_reverse ;
  address g_root_vault ; // the kind of merchandise being bought
  address g_owner_vault ; // the auction vault were the merchandise should be store
  
  function _init_auction(
                         string kind,
                         uint256 owner_pubkey,
                         address owner_address,
                         address root_wallet,
                         uint256 time_stop,
                         address owner_vault
           ) internal
  {

    require( address(this).balance >= OCP_Constants.MINIMAL_INITIAL_BALANCE
             , OCP_Constants.EXN_NOT_ENOUGH_BALANCE );

    require( g_owner_pubkey == 0 && g_owner_address.value == 0
             , OCP_Constants.EXN_ALREADY_INITIALIZED );

    require( ( s_owner_address.value != 0 && msg.sender == s_owner_address )
             ||
             ( msg.pubkey() != 0 && msg.pubkey() == tvm.pubkey() )
             , OCP_Constants.EXN_AUTH_FAILED );

    if( owner_address.value == 0 ){
      require( s_owner_address.value != 0, OCP_Constants.EXN_INVALID_ARGUMENT );
      owner_address = s_owner_address ;
    }

    require( time_stop >= now
            , OCP_Constants.EXN_INVALID_ARGUMENT );

    tvm.accept();
    g_owner_pubkey = owner_pubkey ;
    g_owner_address = owner_address ;
    g_root_wallet = IRootTokenContract(root_wallet) ;
    g_time_stop = time_stop ;
    g_kind = kind + "auction" ;

    if ( g_root_wallet.value != 0 ){

      IRootTokenContract( g_root_wallet ).
        deployEmptyWallet(
                          OCP_Constants.DEPLOY_WALLET_GRAMS,
                          0,
                          address(this),
                          address(this)
                          ) ;
      IRootTokenContract( g_root_wallet ).getWalletAddress{
          value: OCP_Constants.QUERY_ADDRESS_GRAMS,
          callback:set_wallet_address
      }(
                                                              0,
                                                              address(this)
                                                              );

    }

    if ( owner_vault.value != 0 ){

      g_reverse = true ;
      g_owner_vault = owner_vault ;
      ITONTokenWallet( owner_vault ).getDetails{
        value: OCP_Constants.QUERY_ADDRESS_GRAMS,
        callback:set_root_vault
      }();

    }
  }

  function sendTransaction(
                           address dest,
                           uint128 value,
                           bool bounce,
                           uint8 flags,
                           TvmCell payload) public view
  {
    _only_after_close () ;
    _only_owner_or_winner () ;
    tvm.accept();
    dest.transfer(value, bounce, flags, payload);
  }

  function set_root_vault(ITONTokenWallet.ITONTokenWalletDetails details) public
  {
    require( msg.sender.value != 0 && msg.sender == g_owner_vault,
             OCP_Constants.EXN_AUTH_FAILED );
    g_root_vault = details.root_address ;
  }

  function set_wallet_address( address wallet_address ) public
  {
    require(
            g_root_wallet.value != 0
            && msg.sender == g_root_wallet , OCP_Constants.EXN_AUTH_FAILED );
    tvm.accept() ;
    g_auction_wallet = wallet_address ;
    ITONTokenWallet( g_auction_wallet ).
      setReceiveCallback( address(this), false );
  }

  function _tokens_received( uint128 amount,
                             address sender_wallet,
                             uint256 sender_public_key,
                             address sender_address ) internal virtual ;

  function tokensReceivedCallback(
                                  address /*token_wallet*/,
                                  address /*token_root*/,
                                  uint128 amount,
                                  uint256 sender_public_key,
                                  address sender_address,
                                  address sender_wallet,
                                  address /*original_gas_to*/,
                                  uint128 /*updated_balance*/,
                                  TvmCell /*payload*/
    ) public override
  {
    require( msg.sender.value != 0, OCP_Constants.EXN_AUTH_FAILED );
    require( msg.sender == g_auction_wallet , OCP_Constants.EXN_AUTH_FAILED );
    _tokens_received( amount, sender_wallet,
                        sender_public_key, sender_address );
  }

  function _only_after_close( ) internal view
  {
    require( g_time_stop < now, OCP_Constants.EXN_AUCTION_NOT_CLOSED );
  }

  function _only_before_close( ) internal view
  {
    require( g_time_stop > now, OCP_Constants.EXN_AUCTION_CLOSED );
  }

  function _is_owner( ) internal view returns (bool)
  {
    return
      ( g_owner_address.value != 0 &&
        msg.sender == g_owner_address )
      ||
      ( g_owner_pubkey != 0 &&
        msg.pubkey() == g_owner_pubkey ) ;
  }

  function _is_winner( ) internal view returns (bool)
  {
    return
      ( g_winner_address.value != 0 &&
        msg.sender == g_winner_address )
      ||
      ( g_winner_pubkey != 0 &&
        msg.pubkey() == g_winner_pubkey ) ;
  }

  function _only_owner( ) internal view
  {
    require( _is_owner (), OCP_Constants.EXN_AUTH_FAILED );
  }

  function _only_owner_or_winner( ) internal view
  {
    if ( g_automatic_winner
         && !g_reverse
         && ( g_winner_address.value == 0
           && g_winner_pubkey == 0 ) ){
      // no winner, winner is automatically former owner
      _only_owner() ;
    } else {
      require( _is_winner(), OCP_Constants.EXN_AUTH_FAILED );
    }
  }

  function set_description ( string title, string description ) public
  {
    _only_before_close () ;
    _only_owner () ;
    tvm.accept();
    g_title = title ;
    g_description = description ;
  }

  function set_winner_pubkey( uint256 pubkey ) public
  {
    _only_after_close () ;
    _only_owner_or_winner () ;
    tvm.accept();
    g_winner_pubkey = pubkey ;
  }

  function set_winner_address( address addr ) public
  {
    _only_after_close () ;
    _only_owner_or_winner () ;
    tvm.accept();
    g_winner_address = addr ;
  }

  function _get_auction () internal view returns ( Auction a )
  {
    a = Auction(
                s_id,
                s_owner_address,

                g_owner_address ,
                g_owner_pubkey ,

                g_time_stop ,
                g_root_wallet ,
                g_auction_wallet ,
                g_reverse ,
                g_root_vault ,
                g_owner_vault ,

                g_winner_address ,
                g_winner_pubkey ,

                g_kind ,
                g_title ,
                g_description
                ) ;
      }

}

