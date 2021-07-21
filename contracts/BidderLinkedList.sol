pragma ton-solidity >=0.44;

import "interfaces/IBidderLinkedList.sol";

contract BidderLinkedList is IBidderLinkedList, Constants {

    address static s_builder;
    Bidder static s_current;
    address next;

    constructor(address next_addr){
        tvm.accept();
        next = next_addr;
    }

    function hasNext() view internal returns(bool){
        return(next != address(0));
    }

    function createNext(Bidder b) internal{
        BidderLinkedList node = 
            new BidderLinkedList
                {
                    value: /* TODO */,
                    code: tvm.code(),
                    varInit:{
                        s_builder: address(this),
                        s_current: b
                    }
                }
                (next);
        next = address(node);
    }

    function getBidder() external view responsible returns(Bidder){
        return s_current;
    }

    function addSortedIncreasingOrder(Bidder b, BidderLinkedList l) override  {
        
        if (b.bid < s_current.bid){
            createNext
        }

        while(tmp.next.hasValue()){
            if (b.bid < tmp.bidder.bid){
                createNext(b);
                return l;
            }
            tmp = tmp.next.get();
        }

        tmp.next.set(create(b));
        return l;
    }

    function addSortedDecreasingOrder(Bidder b, BidderLinkedList l) override returns(BidderLinkedList){
        BidderLinkedList tmp = l;
        
        while(tmp.next.hasValue()){
            if (b.bid > tmp.bidder.bid){
                BidderLinkedList new_node = create(b);
                BidderLinkedList next = tmp.next.get();
                tmp.next.set(new_node);
                new_node.next.set(next);
                return l;
            }
            tmp = tmp.next.get();
        }

        tmp.next.set(create(b));
        return l;
    }

}