pragma ton-solidity >=0.44;

import "interfaces/IBuildable.sol";

contract Buildable is IBuildable {
    function thisIsMyCode() external override responsible returns(TvmCell){
        tvm.accept();
        return {flag: 128} tvm.code();
    }
}