unzip pldi24-36-artifact.zip
sudo docker build -t artifact:latest .
sudo docker save artifact | gzip > ./artifact.tar.gz
rm -rf pldi24-36-artifact/
