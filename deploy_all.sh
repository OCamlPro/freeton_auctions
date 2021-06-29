bash deploy.sh EnglishAuction
bash deploy.sh EnglishReverseAuction
bash deploy.sh DutchAuction
bash deploy.sh DutchReverseAuction
bash deploy.sh AuctionRoot

ft multisig -a user1 --transfer 10 --to AuctionRoot init '{"ec":"%{account:address:EnglishAuction}", "erc":"%{account:address:EnglishReverseAuction}" ,"dc":"%{account:address:DutchAuction}" ,"drc":"%{account:address:DutchReverseAuction}"}'
