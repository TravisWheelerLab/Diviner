#!/usr/bin/env sh


set -e


TOTAL_NUM_TESTS=22
GLOBAL_TEST_NUM=1
LOCAL_TEST_NUM=1


confirm_file_exists()
{
    FILENAME=$1
    if [ ! -e $FILENAME ];
    then
	echo "  Failed to locate file '$FILENAME'"
	exit 1
    fi
}


confirm_identical_files()
{
    FILE1=$1
    FILE2=$2
    TEST_TYPE=$3
    DIFF=$(diff $FILE1 $FILE2)
    DIFF_EXIT_CODE=$?
    if [ $DIFF_EXIT_CODE -ne 0 ];
    then
	echo "\n    ERROR ($TEST_TYPE): Files '$FILE1' and '$FILE2' do not match"
	exit 1
    fi
}


report_test_start()
{
    TEST_TYPE=$1
    printf '  [diviner dependencies test '
    if [ $GLOBAL_TEST_NUM -lt 10 ];
    then
	printf ' '
    fi
    printf "$GLOBAL_TEST_NUM/$TOTAL_NUM_TESTS]: $TEST_TYPE test $LOCAL_TEST_NUM..."
    GLOBAL_TEST_NUM=$(($GLOBAL_TEST_NUM + 1))
    LOCAL_TEST_NUM=$(($LOCAL_TEST_NUM + 1))
}


# sindex testing
check_sindex()
{
    FILE_NAME=$1

    INPUT_FILE=$INPUTS_DIR/$FILE_NAME
    OBSERVED_FILE=$INPUTS_DIR/$FILE_NAME.hsi
    EXPECTED_FILE=$EXP_OUTPUTS_DIR/$FILE_NAME.hsi

    if [ -e $OBSERVED_FILE ];
    then
	rm $OBSERVED_FILE
    fi

    report_test_start sindex
    $SINDEX $INPUT_FILE
    confirm_identical_files $OBSERVED_FILE $EXPECTED_FILE sindex
    echo ' passed'
}


# sstat
check_sstat()
{
    FILE_NAME=$1

    INPUT_FILE=$INPUTS_DIR/$FILE_NAME
    OBSERVED_FILE=$OBS_OUTPUTS_DIR/$FILE_NAME.sstat
    EXPECTED_FILE=$EXP_OUTPUTS_DIR/$FILE_NAME.sstat

    report_test_start sstat
    $SSTAT $INPUT_FILE > $OBSERVED_FILE
    confirm_identical_files $OBSERVED_FILE $EXPECTED_FILE sstat
    echo ' passed'
}


# sfetch
check_sfetch()
{
    RANGE_OPT=$1
    SEQ_NAME=$2
    IN_FILE_NAME=$3
    OUT_FILE_NAME=$4

    INPUT_FILE=$INPUTS_DIR/$IN_FILE_NAME
    OBSERVED_FILE=$OBS_OUTPUTS_DIR/$OUT_FILE_NAME
    EXPECTED_FILE=$EXP_OUTPUTS_DIR/$OUT_FILE_NAME

    report_test_start sfetch
    $SFETCH $RANGE_OPT $INPUT_FILE $SEQ_NAME > $OBSERVED_FILE
    confirm_identical_files $OBSERVED_FILE $EXPECTED_FILE sfetch
    echo ' passed'
}


check_tblastn()
{
    DNA_NAME=$1
    AMINO_NAME=$2
    OUT_FILE_NAME=$3

    DNA_INPUT=$INPUTS_DIR/$DNA_NAME
    AMINO_INPUT=$INPUTS_DIR/$AMINO_NAME
    OBSERVED_FILE=$OBS_OUTPUTS_DIR/$OUT_FILE_NAME
    EXPECTED_FILE=$EXP_OUTPUTS_DIR/$OUT_FILE_NAME

    report_test_start tblastn
    $TBLASTN -outfmt 6 -subject $DNA_INPUT -query $AMINO_INPUT -out $OBSERVED_FILE 1>/dev/null
    confirm_identical_files $OBSERVED_FILE $EXPECTED_FILE tblastn
    echo ' passed'
}


HSI_BASE=hsi
TBLASTN_BASE=tblastn

DEPS_DIR=dependencies

TEST_DIR=$DEPS_DIR/install-test
HSI_DIR=$DEPS_DIR/$HSI_BASE-1.0.0
TBLASTN_DIR=$DEPS_DIR/$TBLASTN_BASE

TEST_TAR=$TEST_DIR.tgz
HSI_TAR=$HSI_DIR.tgz
TBLASTN_TAR=$TBLASTN_DIR.tgz

confirm_file_exists $TEST_TAR
confirm_file_exists $HSI_TAR
confirm_file_exists $TBLASTN_TAR

BUILD_DIR=build

# Because we want to be sure that everything we're testing has been
# unpacked and setup in this specific environment
rm -rf $TEST_DIR
rm -rf $HSI_DIR
rm -rf $TBLASTN_DIR

# Test input and output files
tar -xf $TEST_TAR -C $DEPS_DIR
INPUTS_DIR=$TEST_DIR/inputs
EXP_OUTPUTS_DIR=$TEST_DIR/outputs-expected
OBS_OUTPUTS_DIR=$TEST_DIR/outputs-observed

# We want to make sure we're looking at a clean slate of observations
rm -rf $OBS_OUTPUTS_DIR
mkdir $OBS_OUTPUTS_DIR

AA1_NAME=sp1.aa.fa
AA2_NAME=sp2.aa.fa
AA3_NAME=sp3.aa.fa
AA123_NAME=123.aa.fa

DNA1_NAME=sp1.dna.fa
DNA2_NAME=sp2.dna.fa
DNA3_NAME=sp3.dna.fa

GTF1=$INPUTS_DIR/sp1.gtf
GTF2=$INPUTS_DIR/sp2.gtf
GTF3=$INPUTS_DIR/sp3.gtf
SPECIES_GUIDE=$INPUTS_DIR/species-guide

confirm_file_exists $INPUTS_DIR/$AA1_NAME
confirm_file_exists $INPUTS_DIR/$AA2_NAME
confirm_file_exists $INPUTS_DIR/$AA3_NAME
confirm_file_exists $INPUTS_DIR/$AA123_NAME
confirm_file_exists $INPUTS_DIR/$DNA1_NAME
confirm_file_exists $INPUTS_DIR/$DNA2_NAME
confirm_file_exists $INPUTS_DIR/$DNA3_NAME
confirm_file_exists $GTF1
confirm_file_exists $GTF2
confirm_file_exists $GTF3
confirm_file_exists $SPECIES_GUIDE



# 1 HSI
if [[ -d $BUILD_DIR/$HSI_BASE ]]
then
    echo " HSI already built (remove $BUILD_DIR/$HSI_BASE to remake)"
else
    tar -xf $HSI_TAR -C $DEPS_DIR
    cd $HSI_DIR && cmake . && make && cd -

    SINDEX=$HSI_DIR/build/sindex
    SSTAT=$HSI_DIR/build/sstat
    SFETCH=$HSI_DIR/build/sfetch

    LOCAL_TEST_NUM=1
    check_sindex $AA1_NAME    # test 1
    check_sindex $AA2_NAME    # test 2
    check_sindex $AA3_NAME    # test 3
    check_sindex $AA123_NAME  # test 4
    check_sindex $DNA1_NAME   # test 5
    check_sindex $DNA2_NAME   # test 6
    check_sindex $DNA3_NAME   # test 7

    LOCAL_TEST_NUM=1
    check_sstat $AA1_NAME    # test  8
    check_sstat $AA2_NAME    # test  9
    check_sstat $AA3_NAME    # test 10
    check_sstat $AA123_NAME  # test 11
    check_sstat $DNA1_NAME   # test 12
    check_sstat $DNA2_NAME   # test 13
    check_sstat $DNA3_NAME   # test 14

    SP1_GENE2_DNA_NAME=sp1.g2.dna.fa
    SP1_GENE3_DNA_NAME=sp1.g3.dna.fa
    SP2_GENE2_DNA_NAME=sp2.g2.dna.fa
    SP2_GENE3_DNA_NAME=sp2.g3.dna.fa
    SP3_GENE23_DNA_NAME=sp3.g23.dna.fa

    LOCAL_TEST_NUM=1
    check_sfetch '-range 16000..38000' chr1 $DNA1_NAME $SP1_GENE2_DNA_NAME   # test 15
    check_sfetch '-range 1000..27000'  chr2 $DNA1_NAME $SP1_GENE3_DNA_NAME   # test 16
    check_sfetch '-range 13000..38000' chr1 $DNA2_NAME $SP2_GENE2_DNA_NAME   # test 17
    check_sfetch '-range 24000..1000'  chr2 $DNA2_NAME $SP2_GENE3_DNA_NAME   # test 18
    check_sfetch '-range 13000..64500' chr1 $DNA3_NAME $SP3_GENE23_DNA_NAME  # test 19

    mv -f $HSI_DIR $BUILD_DIR/$HSI_BASE
fi


# TBLASTN
if [[ -d $BUILD_DIR/$TBLASTN_BASE ]]
then
    echo " Tblastn already built (remove $BUILD_DIR/$TBLASTN to remake)"
else
    tar -xf $TBLASTN_TAR -C $DEPS_DIR
    TBLASTN=$TBLASTN_DIR/tblastn.linux.x86_64
    
    LOCAL_TEST_NUM=1
    check_tblastn $DNA1_NAME $AA1_NAME sp1.tblastn.out  # test 20
    check_tblastn $DNA2_NAME $AA2_NAME sp2.tblastn.out  # test 21
    check_tblastn $DNA3_NAME $AA3_NAME sp3.tblastn.out  # test 22

    mv -f $TBLASTN_DIR $BUILD_DIR/$TBLASTN_BASE
fi


# Cleanup
rm -rf $TEST_DIR
echo "    All dependencies passed!"


# END OF SCRIPT
