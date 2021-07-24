import "V_OCP_Auction.sol" ;

abstract contract V_OCP_AuctionSetcode is V_OCP_Auction {

  function set_winner_code ( TvmCell code ) public
  {
    _only_after_close () ;
    _only_owner_or_winner () ;
    tvm.accept();
    tvm.setcode(code);
    tvm.setCurrentCode(code);
    onCodeUpgrade();
  }

  function onCodeUpgrade() private
  {
    tvm.resetStorage();
  }

}
