
interface IBlindBid is IBid {
    function reveal(uint256 salt, uint256 amount) external;
}