
interface I_OCP_ReverseAuction {

  function bid( uint128 amount,
                address bidder_wallet,
                uint256 bidder_pubkey,
                address bidder_vault ) external;

}
