pip install -q gdown

if [ ! -d "./Isabelle2024" ]; then
    echo "Downloading Isabelle2024"
    gdown --fuzzy https://drive.google.com/file/d/1-cdF3SZoqtlhWTbqlgMT9h4S5T8LRvLK/view?usp=sharing -O ./downloads/Isabelle2024_linux.tar.gz
    echo "Unpacking Isabelle2024"
    tar -xzf ./downloads/Isabelle2024_linux.tar.gz
fi

if [ ! -d "./afp-2025-02-12" ]; then
    echo "Downloading AFP"
    gdown --fuzzy https://drive.google.com/file/d/1_iuUpTg-AsahixhIJkmBOlFGsnzvoovx/view?usp=sharing -O ./downloads/afp-2025-02-12.tar.gz
    echo "Unpacking AFP"
    tar -xzf ./downloads/afp-2025-02-12.tar.gz
fi

PATH=./Isabelle2024/bin:$PATH
rm -f  $(isabelle getenv -b ISABELLE_HOME_USER)/etc/components 2>/dev/null
isabelle components -u ./afp-2025-02-12/thys

NPROC=$(nproc)

echo "Building AFP-DEP1"
isabelle build -b -D ./Build_AFP_Image/AFP-DEP1 -o threads=$NPROC AFP-DEP1