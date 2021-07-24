pragma ton-solidity >=0.44;

import "interfaces/IBuildable.sol";

// A small contract to inherit for sharing one's own code
//
// WARNING
// Must only be inherited by contract that are NOT SUPPOSED TO HOLD TOKENS

contract Buildable is IBuildable {

    // Shares its own code.
    function thisIsMyCode() external override responsible returns(TvmCell){
        tvm.accept();
        return {flag: 128} tvm.code();
    }

}