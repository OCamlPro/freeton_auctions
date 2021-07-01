pragma ton-solidity >=0.44;

interface IAuction {
    function bid(uint256) external;
    function submit(uint256) external; // Appelé que par un BID 
    function thisIsMyCode() external responsible returns(TvmCell);
}