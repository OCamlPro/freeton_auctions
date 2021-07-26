
interface I_OCP_BlindAuction {

  function bid(
               uint128 amount, uint64 blind_time, uint128 price_start,
               uint64 nonce,
               address bidder_address, uint256 bidder_pubkey ) external ;
}
