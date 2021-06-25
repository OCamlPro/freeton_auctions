pragma ton-solidity >=0.44;

interface IEnglishAuction {
    function bid(uint32 callback_refund, uint32 callback_winner) external;
    function endAuction() external;
}