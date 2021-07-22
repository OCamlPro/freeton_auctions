ft multisig transfer 5 --from user1 --to AuctionRoot deployDutchAuction '{"root_wallet":"%{account:address:CrystalRootWallet}", "winner_processor":"%{account:address:CrystalProcessWinner}", "start_price":"1000", "end_price": "7", "price_delta": "10", "time_delta": 1}' &&

auction_list=($(ft inspect --past AuctionRoot 2>&1 | grep 'Event AuctionCreated' | sed 's/.*\"auction\":\"//g' | sed 's/\".*//g')) &&
bid_builder_list=($(ft inspect --past AuctionRoot 2>&1 | grep 'Event AuctionCreated' | sed 's/.*\"bid_builder\":\"//g' | sed 's/\".*//g')) &&

auction=${auction_list[-1]} &&
bid_builder=${bid_builder_list[-1]} &&
echo "Auction = $auction, BidBuilder = $bid_builder" &&

data="{\"bid_builder\":\"${bid_builder}\",\"auction_address\":\"${auction}\",\"blind\":\"false\"}"

echo "Data = $data"

set -x

ft account create DutchAuctionInstance --contract DutchAuction --address $auction -f &&
ft account create BidBuilderInstance --contract BidBuilder --address $bid_builder -f &&
ft multisig transfer 5 --from user1 --to AuctionRoot initBidBuilder $data &&
ft multisig transfer 5 --from user1 --to DutchAuctionInstance bid '{"commitment":"990"}'

bid_list=($(ft inspect --past BidBuilderInstance 2>&1 | grep 'Event ThisIsYourBid' | sed 's/.*\"bid\":\"//g' | sed 's/\".*//g'))

bid=${bid_list[-1]}

ft account create BidInstance --contract Bid --address $bid
