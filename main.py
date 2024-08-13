import sys
from PyQt5 import QtWidgets

from PyQt5.QtWidgets import QApplication, QMainWindow, QWidget, QVBoxLayout, QLabel, QPushButton, QFileDialog
import os
import io
import xml.etree.ElementTree as ET
from tqdm.auto import tqdm
import pandas as pd
from datetime import datetime, timedelta
import itertools
import threading
import time
import sys
import pyodbc
import ast
import configparser
import psutil
import gc
import traceback
import linecache
from difflib import SequenceMatcher
import csv
import re
import nltk
from nltk.corpus import words
import shutil
import glob

tqdm.pandas()

# Download necessary NLTK resources if not already available, and load English words into a set for quick lookup
nltk.download('words', quiet=True)
english_words = set(words.words())

# Read parameters from the config file
config = configparser.ConfigParser()
config.read('goaml_config.ini')

reporting_window = config['DEFAULT'].getint('ReportingWindow')
report_start_date = config['DEFAULT']['ReportStartDate']
report_end_date = config['DEFAULT']['ReportEndDate']
ctr_threshold = config['DEFAULT'].getfloat('CTRThreshold')
report_types = [report_type.strip() for report_type in config.get('DEFAULT', 'ReportTypes').split(',')]
incorp_number_reg_types = [incorp_number.strip() for incorp_number in config.get('DEFAULT', 'IncorpNumberRegTypes').split(',')]
invalid_acc_prefixes = [prefix.strip() for prefix in config.get('INVALID_DATA', 'InvalidAccPrefixes').split(',')]
invalid_acc_chars = [prefix.strip() for prefix in config.get('INVALID_DATA', 'InvalidAccChars').split(',')]
swift_name_match_threshold = config['DEFAULT'].getfloat('SwiftNameMatchThreshold')
check_late_submissions = config['DEFAULT'].getboolean('CheckLateSubmissions')

# System control parameters to ensure smooth operation (such as memory management, Excel row limit, etc.)
memory_threshold_break = config['SYSTEM_DATA'].getint('MemoryThresholdBreak')
memory_threshold_clean = config['SYSTEM_DATA'].getint('MemoryThresholdGC')
max_rows_excel = config['SYSTEM_DATA'].getint('MaxRowsExcel')

# Reporting Entity Data
report_entity_id = config['RE_DATA'].getint('ReportingEntityID')
report_entity_name = config['RE_DATA'].get('ReportingEntityName')
report_entity_swift = config['RE_DATA'].get('ReportingEntitySwift')

swift_codes_dict = {}
with open('./RE_swift_codes.csv', mode='r', encoding='utf-8-sig') as csvfile:
     reader = csv.reader(csvfile)
     for row in reader:
        key, value = row[0], row[1]
        if key in swift_codes_dict:
            swift_codes_dict[key].append(value)  # Append to existing list
        else:
            swift_codes_dict[key] = [value]  # Create a new list for this key      
swift_codes = list(swift_codes_dict.keys())



# Global variables used in validator functions and main function
issues_file_name = ''

# Specify the local folder path where XML files should be saved
local_folder_path = ''
output_path=''
reporting_issues = []
issues_upload_ids = []
report_entity_name="NDB Securities"
report_entity_id="001"
report_entity_swift="001"
details=''


def memory_usage():
    process = psutil.Process()
    return process.memory_info().rss / (1024 * 1024)  # Convert bytes to MB

# Helper function to check if a string is considered valid
def is_valid(value):
    return value is not None and value.strip() != ''

# Helper function to parse a date in the format 'YYYY-MM-DDTHH:MM:SS'
def parse_date(date_string):
    # Remove the fractional part of the timestamp if it exists
    date_string = date_string.split('.')[0]  # Keep only the part before the decimal point
    
    # First format (with time)
    try:
        return datetime.strptime(date_string, '%Y-%m-%dT%H:%M:%S').date()
    except ValueError:
        # If parsing with the first format fails, try the second format (date only)
        try:
            return datetime.strptime(date_string, '%Y-%m-%d').date()
        except ValueError:
            # If both attempts fail, return None
            return None


# Helper function to get numeric value from an xml element
def get_numeric_value(element):
    if element is not None and element.text is not None:
        text = element.text.strip()  # Strip leading/trailing whitespace
        try:
            # Try converting to float
            return float(text)
        except ValueError:
            # Handle the case where conversion fails
            return None
    else:
        return None
    
# Helper function to safely convert a string representation of a list into an actual list
# If the input is a plain string (not a list representation), it's converted into a list with that string as a single element
def parse_list(val):
    if isinstance(val, str):
        try:
            # Try to parse the string into a list using ast.literal_eval
            parsed_val = ast.literal_eval(val)
            # Ensure the parsed value is indeed a list, if not, encapsulate it in a list
            return parsed_val if isinstance(parsed_val, list) else [val]
        except (ValueError, SyntaxError):
            # If parsing fails, assume it's a plain string and return it as a single-element list
            return [val]
    elif isinstance(val, list):
        # If it's already a list, return as is
        return val
    else:
        # For NaN or other types, return an empty list
        return []
    
# Helper function to identify words in a string (account number)
def find_english_words(text):
    found_words = set()

    # Convert to uppercase for consistent checking, as word list might be in lowercase
    text = text.upper()

    # Check every possible substring that is longer than 4 characters
    for start in range(len(text)):
        for end in range(start + 5, len(text) + 1):  # start + 5 ensures minimum length of 5
            substring = text[start:end]
            if substring.lower() in english_words:
                found_words.add(substring)

    return found_words
    
# Function to validate the transaction date
def is_valid_transaction_date(transaction_date, submission_date):
    if transaction_date is not None and submission_date is not None:
        # Transaction date cannot be after submission date, or before goAML reporting start date (01/01/2022)
        return (transaction_date <= submission_date) & (transaction_date >= parse_date('2022-01-01'))
    return False

# Function to check late submissions
def is_late_submission(transaction_date, submission_date):
    if transaction_date is not None and submission_date is not None:
        # Submission date should be within 31 days from transaction date
        diff = submission_date - transaction_date
        diff_days = diff.days
        return (diff_days > reporting_window)
       
# Function to validate ssn  
def validate_ssn(tpe_ssn):
    if tpe_ssn is None:
        return False

    length = len(tpe_ssn)

    # Rule for 9 number + English letter format
    if (length == 10 or (length == 11 and tpe_ssn.find(' ') == 9)):
        if ('10' <= tpe_ssn[:2] <= '99' and
                ('001' <= tpe_ssn[2:5] <= '366' or '501' <= tpe_ssn[2:5] <= '866') and
                tpe_ssn[-1].upper() in ['V', 'X']):
            return True

    # Rule for 12 number format
    elif length == 12:
        if ('1910' <= tpe_ssn[:4] <= '2010' and
                ('001' <= tpe_ssn[4:7] <= '366' or '501' <= tpe_ssn[4:7] <= '866')):
            return True

    return False
       
# Function to check whether a transaction has accounts in both From and To sides
def is_accounts_both_side(transaction):
    is_from_account = False
    is_to_account = False
    
    # Not checking the From and To sides if transaction is multi-party. Simply return true
    involved_parties = transaction.find('involved_parties')
    if involved_parties is not None:
        return False
    
    t_from_my_client = transaction.find('t_from_my_client')
    t_from = transaction.find('t_from')
    t_to_my_client = transaction.find('t_to_my_client')
    t_to = transaction.find('t_to')
    
    if t_from_my_client is not None:
        from_account = t_from_my_client.find('from_account')
        if from_account is not None:
            is_from_account = True
    
    elif t_from is not None:
        from_account = t_from.find('from_account')
        if from_account is not None:
            is_from_account = True  
            
    if t_to_my_client is not None:
        to_account = t_to_my_client.find('to_account')
        if to_account is not None:
            is_to_account = True
       
    elif t_to is not None:
        to_account = t_to.find('to_account')
        if to_account is not None:
            is_to_account = True
        
    return (is_from_account & is_to_account)

# Function to check whether a transaction has accounts in any of From and To sides
def is_accounts_any_side(transaction):
    is_from_account = False
    is_to_account = False
    
    # Not checking the From and To sides if transaction is multi-party. Simply return true
    involved_parties = transaction.find('involved_parties')
    if involved_parties is not None:
        return True
    
    t_from_my_client = transaction.find('t_from_my_client')
    t_from = transaction.find('t_from')
    t_to_my_client = transaction.find('t_to_my_client')
    t_to = transaction.find('t_to')
    
    if t_from_my_client is not None:
        from_account = t_from_my_client.find('from_account')
        if from_account is not None:
            is_from_account = True
    
    elif t_from is not None:
        from_account = t_from.find('from_account')
        if from_account is not None:
            is_from_account = True  
            
    if t_to_my_client is not None:
        to_account = t_to_my_client.find('to_account')
        if to_account is not None:
            is_to_account = True
       
    elif t_to is not None:
        to_account = t_to.find('to_account')
        if to_account is not None:
            is_to_account = True
        
    return (is_from_account | is_to_account)
    
# Function to check whether a transaction has country LK in both From and To sides
def is_both_sides_LK(transaction):
    is_from_LK = False
    is_to_LK = False
    
    # Not checking the From and To sides if transaction is multi-party. Simply return true
    involved_parties = transaction.find('involved_parties')
    if involved_parties is not None:
        return False
    
    t_from_my_client = transaction.find('t_from_my_client')
    t_from = transaction.find('t_from')
    t_to_my_client = transaction.find('t_to_my_client')
    t_to = transaction.find('t_to')
    
    if t_from_my_client is not None:
        from_country_element = t_from_my_client.find('from_country')
        if from_country_element is not None:
            from_country = from_country_element.text
            if from_country == 'LK':
                is_from_LK = True
    
    elif t_from is not None:
        from_country_element = t_from.find('from_country')
        if from_country_element is not None:
            from_country = from_country_element.text
            if from_country == 'LK':
                is_from_LK = True
                    
    if t_to_my_client is not None:
        to_country_element = t_to_my_client.find('to_country')
        if to_country_element is not None:
            to_country = to_country_element.text
            if to_country == 'LK':
                is_to_LK = True
                    
    elif t_to is not None:
        to_country_element = t_to.find('to_country')
        if to_country_element is not None:
            to_country = to_country_element.text
            if to_country == 'LK':
                is_to_LK = True
                    
    return (is_from_LK & is_to_LK)


# Function to validate swift code of an account's Institution with its Institution name
def is_swift_bank_match(swift_code, institution_name, similarity_threshold=0.75):
    institution_name_lower = institution_name.lower()

    for key, values in swift_codes_dict.items():
        if swift_code.upper().startswith(key):
            for value in values:
                # Calculate similarity for each institution name associated with the SWIFT code
                match_ratio = SequenceMatcher(None, institution_name_lower, value.lower()).ratio()
                if match_ratio > similarity_threshold:
                    return True
    return False
        
       
# Function to validate a person

# my_client person nationality1 presence check
# my_client person ssn presence check for sri lankans
# my_client person ssn validity check (as per numbering format) for sri lankans
# my_client person passport number presence for foreigners (nationality1 not 'LK')
# my_client person other mandatory elements presence check

# not_my_client person first_name and last_name elements presence check
# not_my_client person nationality1 presence check for in branch and agent transactions
# not_my_client person ssn presence check for sri lankans for in branch and agent transactions
# not_my_client person ssn validity check for sri lankans for in branch and agent transactions
# not_my_client person passport number presence check for foreigners for in branch and agent transactions
# not_my_client person key fields presence check to identify submission of my_clients as not_my_clients

# director person first_name and last_name elements presence check
# director person nationality1 presence check for in branch and agent transactions
# director person ssn presence check for sri lankans
# director person ssn validity check for sri lankans
# director person passport number presence check for foreigners

def validate_person(person, client_type, transmode):
    # Variable to hold and log the name of the last element when an exception is thrown (for troubleshooting general exceptions)
    check_element = ''
    
    # Array to hold validation error messages for each element in person. 
    # This function goes through all elements and recrod invalid elements 
    error_message = []
    
    try:
        # My client persons
        if client_type == 'my_client':
            check_element = 'first_name'
            first_name = person.find('first_name').text
            
            check_element = 'last_name'
            last_name = person.find('last_name').text
            
            check_element = 'birthdate'
            birthdate = person.find('birthdate').text
            
            # For my client persons, nationality1 is mandatory
            check_element = 'nationality1'
            nationality1_element = person.find('nationality1')
            if nationality1_element is None:
                error_message.append('my_client person nationality1 not given')
            else:
                nationality1 = nationality1_element.text
                if nationality1 == 'LK':
                    # For sri lankan my client persons, ssn is mandatory
                    # (there can be rare exceptions, but validated in general)
                    check_element = 'ssn'
                    ssn_element = person.find('ssn')
                    if ssn_element is None:
                        error_message.append('my_client LK person NIC not given in <ssn>')
                    else:
                        ssn = ssn_element.text
                        if not validate_ssn(ssn):
                            error_message.append(f'my_client LK person NIC {ssn} invalid')
                     
                # nationality1 is not 'LK'
                else:
                    # For foreign my client persons, passport number is mandatory
                    # (there can be rare exceptions, but validated in general)
                    check_element = 'passport_number'
                    passport_element = person.find('passport_number')
                    if passport_element is None:
                        error_message.append('my_client foreign person passport not given in <passport_number>')
                    else:
                        # Passport number is not validated like ssn
                        passport_number = passport_element.text
            
            # Validate other elements
            check_element = 'residence'
            residence = person.find('residence').text
            
            check_element = 'occupation'
            occupation = person.find('occupation').text

            check_element = 'addresses'
            addresses_element = person.find('addresses')
            
            check_element = 'address'
            address_element = addresses_element.find('address')
            
            check_element = 'address_address'
            address = address_element.find('address').text
            
            check_element = 'address_city'
            city = address_element.find('city').text
            
            check_element = 'address_country'
            country = address_element.find('country_code').text
                        
        # Not my client persons
        elif client_type == 'not_my_client':
            check_element = 'first_name'
            first_name = person.find('first_name').text
            
            check_element = 'last_name'
            last_name = person.find('last_name').text
            
            if transmode == 'BRCH' or transmode == 'AGNT':
                # For not my client inbranch and agent handled persons, nationlity is mandatory
                # (there can be rare exceptions, but validated in general)
                check_element = 'nationality1'
                nationality1_element = person.find('nationality1')
                if nationality1_element is None:
                    error_message.append('not_my_client BRCH or AGNT person nationality1 not given')
                else:
                    nationality1 = nationality1_element.text
                    if nationality1 == 'LK':
                        # For not my client inbranch sri lankan persons, ssn is mandatory
                        check_element = 'ssn'
                        ssn_element = person.find('ssn')
                        if ssn_element is None:
                            error_message.append('not_my_client BRCH or AGNT LK person NIC not given in <ssn>')
                        else:
                            ssn = ssn_element.text
                            if not validate_ssn(ssn):
                                error_message.append(f'not_my_client BRCH or AGNT LK person NIC {ssn} invalid')
                    
                    # nationality1 is not 'LK'
                    else:
                        # For not my client inbranch foreign persons, passport number is mandatory
                        # (there can be rare exceptions, but validated in general)
                        check_element = 'passport_number'
                        passport_element = person.find('passport_number')
                        if passport_element is None:
                            error_message.append('not_my_client BRCH or AGNT foreign person passport not given in <passport_number>')
                        else:
                            passport_number = passport_element.text
            
            # transmode is not BRCH
            else:
                # If any of ssn, occupation, dob, address is present, it could indicate a my client person reported as not my client
                ssn_element = person.find('ssn')
                occupation = person.find('occupation')
                birthdate = person.find('birthdate')
                addresses_element = person.find('addresses')
                
                if ssn_element is not None or occupation is not None or birthdate is not None or addresses_element is not None:
                    error_message.append('my_client person <<may be>> submitted as not_my_client')
            
        # Entity director persons
        elif client_type == 'director':
            check_element = 'first_name'
            first_name = person.find('first_name').text
            
            check_element = 'last_name'
            last_name = person.find('last_name').text
            
            check_element = 'nationality1'
            nationality1_element = person.find('nationality1')
            if nationality1_element is None:
                error_message.append('director person nationality1 not given')
            else:
                nationality1 = nationality1_element.text
                if nationality1 == 'LK':
                    # For sri lankan my client persons, ssn is mandatory
                    # (there can be rare exceptions, but validated in general)
                    check_element = 'ssn'
                    ssn_element = person.find('ssn')
                    if ssn_element is None:
                        error_message.append('director LK person NIC not given in <ssn>')
                    else:
                        ssn = ssn_element.text
                        if not validate_ssn(ssn):
                            error_message.append(f'director LK person NIC {ssn} invalid')
                     
                # nationality1 is not 'LK'
                else:
                    # For foreign my client persons, passport number is mandatory
                    # (there can be rare exceptions, but validated in general)
                    check_element = 'passport_number'
                    passport_element = person.find('passport_number')
                    if passport_element is None:
                        error_message.append('director foreign person passport not given in <passport_number>')
                    else:
                        # Passport number is not validated like ssn
                        passport_number = passport_element.text
                        
    except Exception as e:
        error_message.append(f'check_element: {check_element} [Error: {str(e)}]')
    
    # If there are no error messages, it means the perosn is valid
    if not error_message:
        return 'valid'
    else:
        return error_message
    
        
# Function to validate an entity

# entity_name element presence check for my_client and not_my_client entities
# my_client entity incorporation_number element presence check for required legal forms
# my_client entity directors element presence check and validate each director
# my_client entity other mandatory elements presence check

# not_my_client entity not validated (other than for name)

def validate_entity(entity, is_my_client):
    # Variable to hold and log the name of the last element when an exception is thrown (for troubleshooting general exceptions)
    check_element = ''
        
    # Array to hold validation error messages for each element in entity. 
    # This function goes through all elements and record invalid elements 
    error_message = []
    
    try:
        check_element = 'entity_name'
        entity_name = entity.find('name').text
        
        # My client entities
        if is_my_client:
            check_element = 'legal_form'
            legal_form = entity.find('incorporation_legal_form').text
            
            # Incorporation number is mandatory for the selected entity types
            if legal_form in incorp_number_reg_types:
                check_element = 'incorporation_number'
                incorporation_number_element = entity.find('incorporation_number')
                if incorporation_number_element is None:
                    error_message.append('entity incorp number not given for required types')
                else:
                    incorporation_number = incorporation_number_element.text
            
            check_element = 'business'
            business = entity.find('business').text

            check_element = 'incorporation_country'
            incorp_country = entity.find('incorporation_country_code').text

            check_element = 'addresses'
            addresses_element = entity.find('addresses')
            
            check_element = 'address'
            address_element = addresses_element.find('address')
            
            check_element = 'address_address'
            address = address_element.find('address').text
            
            check_element = 'address_city'
            city = address_element.find('city').text
            
            check_element = 'address_country'
            country = address_element.find('country_code').text
            
            # Director details are not mandatory for government entities
            if legal_form != 'GOVT':
                check_element = 'director_id'
                directors = entity.find('director_id')
                if directors is None:
                    error_message.append('my_client entity directors not given non-gov entity')
                else:
                    for director in directors.findall('t_person'):
                        # Validate each director person
                        director_valid_result = validate_person(person=director, client_type='director', transmode=None)
                        if director_valid_result != 'valid':
                            # Extend the error_message list with the returned list
                            error_message.extend(director_valid_result)
        
        # Not my client entities. If required, provide code here
        # else:
                      
    except Exception as e:
        error_message.append(f'check_element: {check_element} [Error: {str(e)}]')
    
    # If there are no error messages, it means the entity is valid
    if not error_message:
        return 'valid'
    else:
        return error_message
    
    
# Function to validate an account 

# institution_name, swift_code, account_number elements presence check for my_client and not_my_client accounts
# account_number validity check with a predefined prefix list
# my_client account institution (bank) swift_code and RE swift_code same check (my_client accounts must be owned by RE)
# my_client account t_entity and signatory both elements presence (which is invalid) check
# my_client account t_entity validate if present (corporate accounts)
# my_client account signatories validate if present (retail accounts)
# my_client account other mandatory elements presence check

# not_my_client account institution (bank) swift_code check to detect my_client accounts submissions as no_my_clients

def validate_account(report_code, account, is_my_client, rentity_id):
    # Variable to hold and log the name of the last element when an exception is thrown (for general exceptions)
    check_element = ''
    
    # Array to hold validation error messages for each element in account. 
    # This function goes through all elements and recrod invalid elements 
    error_message = []
    
    try:
        check_element = 'institution_name'
        institution_name = account.find('institution_name').text
        
        check_element = 'account_number'
        account_number = account.find('account').text
        
        # Flag for account number validity check, to ensure only one validation is performed on account number per run
        check_account_number = True
        
        # Check if account number begins with any invalid prefixes
        for prefix in invalid_acc_prefixes:
            if account_number.startswith(prefix):
                error_message.append(f'flagged prefix: {prefix} in account number') 
                check_account_number = False
                
        # Check if account number contains any invalid characters
        if check_account_number:
            for char in invalid_acc_chars:
                if char in account_number:
                    error_message.append(f'flagged character: {char} in account number')
                    check_account_number = False
                
        # Check if account number contains spaces in middle
        if check_account_number:
            if ' ' in account_number.strip():
                    error_message.append(f'flagged character: spaces in account number')
                    check_account_number = False
                
        # Check if there are only three or less digits, and text portion is not a random character sequence
        # If characters are included in the account number, they should be a random sequence rather than words
        # If account number contains English words and very few digits (such as <= 3), it may be invalid
        if check_account_number:
            numbers = re.findall(r'\d', account_number)
            if len(numbers) <= 3:
                # Check if there are English words in account number 
                words_set = find_english_words(account_number)
                if words_set: 
                    error_message.append(f'flagged format: English words with very few digits in account number')
                    check_account_number = False
                
        check_element = 'swift_code'
        swift_code = account.find('swift').text
        
        # Validations for swift code and institution name (only applicable for local account holding institutions)
        if (report_code != 'IFT'):
            # swift code must match the institutions name at least to the defined threshold
            if not is_swift_bank_match(swift_code, institution_name, swift_name_match_threshold):
                error_message.append(f'account with institution swift: {swift_code} does not match with institutions name: {institution_name}')
            
            else:
                if is_my_client:
                    # If my client account institution (bank) SWIFT is not RE's SWIFT, it is an error
                    if not swift_code.startswith(str(report_entity_swift)):
                        error_message.append(f'my_client account institution swift: {swift_code} is not same as RE swift: {report_entity_swift}')
                else:
                    if swift_code.startswith(str(report_entity_swift)):
                        # If 'not my client' account swift code equal to RE swift, it could indicate my client account submitted as not my client
                        error_message.append(f'RE account with institution swift: {swift_code} is submitted as not_my_client')
                    else:
                        # For all REs, 'not my client' account can only belong to another bank or primary dealer
                        if not (('LKLX' in swift_code) or ('LKLC' in swift_code)):
                            error_message.append(f'incorrect account with institution swift code: {swift_code} submitted in not_my_client account')

        # My client accounts
        if is_my_client:            
            check_element = 'branch'
            branch = account.find('branch').text
            check_element = 'currency_code'
            currency_code = account.find('currency_code').text
            check_element = 'account_type'
            account_type = account.find('personal_account_type').text
            check_element = 'status'
            status = account.find('status_code').text
            
            t_entity = account.find('t_entity')
            signatories = account.findall('signatory')
            
            # Entity and person cannot be owners of the same account. No need to further process any element
            if t_entity is not None and signatories:
                error_message.append('t_entity and signatories both given in account')
                return error_message
            
            # Validate corporate account owner entity
            if t_entity is not None:
                check_element = 't_entity'
                # Validate entity
                entity_valid_result = validate_entity(entity=t_entity, is_my_client=True)
                if entity_valid_result != 'valid':
                    # Extend the error_message list with the returned list
                    error_message.extend(entity_valid_result)
            
            # Validate retail account owner person
            if signatories is not None:
                for signatory in signatories:
                    check_element = 'is_primary'
                    is_primary = signatory.find('is_primary')
                    check_element = 'role'
                    role = signatory.find('role')
                    
                    t_person = signatory.find('t_person')
                    check_element = 'signatories'
                    # Validate each signatory person
                    person_valid_result = validate_person(person=t_person, client_type='my_client', transmode=None)
                    if person_valid_result != 'valid':
                        # Extend the error_message list with the returned list
                        error_message.extend(person_valid_result)
            
        # elif (Not my client accounts)
        # Implement code here ...
                      
    except Exception as e:
        error_message.append(f'check_element: {check_element} [Error: {str(e)}]')
    
    # If there are no error messages, it means the account is valid
    if not error_message:
        return 'valid'
    else:
        return error_message
    
# Function to validate a transaction

# Transaction date validate to check it is before submission date or after report date
# Mandatory elements presence check for each section of the transaction
# Validates each transaction for following and stores issues and upload_ids in lists:
# 1. Checks if transaction date is after report start date (defined in goaml_config.ini) and on or before submission date
# 2. Checks if location is given for branch transactions and multi-party credit card transactions
# 3. Checks if amount is above 1 million, below extreme threshold (for CTRs), and not a round number for cash transactions 
# 4. Checks if both From and To sides are not accounts for cash transactions
# 5. Checks if any of From and To sides are account for EFT transactions
# 6. Checks if both From and To sides of IFT transactions are not LK
# 7. Checks if cash transaction from country is LK (for both my_client and not_my_clients)
# 8. Validates Persons, Accounts, Entities (my_client and not_my_clients) using relevant functions
# 9. Checks if amount is not equal to account number 

def process_transaction(transaction_seq, transaction, report_code, upload_id, submission_date):
    # Variable to indicate if the transaction is valid
    is_txn_valid = True
    
    transaction_number = transaction.find('transactionnumber')
    transaction_location = transaction.find('transaction_location')
    transaction_description = transaction.find('transaction_description')
    transaction_date_text = transaction.find('date_transaction').text
    transaction_date = parse_date(transaction_date_text)
    transmode_code = transaction.find('transmode_code').text
    transaction_amount_local = transaction.find('amount_local')
    involved_parties = transaction.find('involved_parties')

    # Validate transaction date
    if not is_valid_transaction_date(transaction_date, submission_date):
        reporting_issues.append({
            'report_name': f'{report_code}: {upload_id}',
            'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
            'category': 'invalid_transaction_date',
            'element': 'date_transaction',
            'issue': f'transaction date: {transaction_date} invalid for submission date: {submission_date}'
        })
        
        # Append upload id of the invalid report to a list for later usage (downloading XML reports)
        issues_upload_ids.append(upload_id)
        # Set the transaction as invalid
        is_txn_valid = False
        
    # Check for late submissions
    if check_late_submissions:
        if is_late_submission(transaction_date, submission_date):
            reporting_issues.append({
            'report_name': f'{report_code}: {upload_id}',
            'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
            'category': 'late_submission',
            'element': 'date_transaction',
            'issue': f'transaction date: {transaction_date} is a late submission for submission date: {submission_date}'
            })
        
            # Append upload id of the invalid report to a list for later usage (downloading XML reports)
            issues_upload_ids.append(upload_id)
            # Set the transaction as invalid
            is_txn_valid = False    

    # Determine if transaction_location is mandatory
    location_mandatory = False
    credit_card_desc = False
    
    # If transmode code is 'BRCH'
    if transmode_code == 'BRCH':
        location_mandatory = True
    # If multi-party and credit card transaction, merchant address should be given in location
    elif involved_parties is not None and transaction_description is not None and transaction_description.text is not None and 'credit card' in transaction_description.text.lower():
        location_mandatory = True
        credit_card_desc = True

    # Check transaction location validity based on the mandatory flag
    if location_mandatory and not is_valid(transaction_location.text if transaction_location is not None else None):
        reporting_issues.append({
            'report_name': f'{report_code}: {upload_id}',
            'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
            'category': 'mandatory but missing/invalid transaction location',
            'element': 'transaction_location',
            'issue': f'transaction location not given for: {transmode_code} and multiparty credit card transaction: {credit_card_desc}'
        })
        
        # Append upload id of the invalid report to a list for later usage (downloading XML reports)
        issues_upload_ids.append(upload_id)
        # Set the transaction as invalid
        is_txn_valid = False

    amount = get_numeric_value(transaction_amount_local)
    
    # Validations for amount
    if amount is not None:
        # Check if amount is below 1 million
        if amount < 1000000:
            reporting_issues.append({
            'report_name': f'{report_code}: {upload_id}',
            'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
            'category': 'amount_below_1_million',
            'element': 'amount_local',
            'issue': f'amount {amount} below LKR 1 Mn'
            })
        
            # Append upload id of the invalid report to a list for later usage (downloading XML reports)
            issues_upload_ids.append(upload_id)
            # Set the transaction as invalid
            is_txn_valid = False
            
        if (report_code == 'CTR'):
            # Check if amount is above extreme valule threshold for cash transactions
            if (amount > ctr_threshold):
                reporting_issues.append({
                'report_name': f'{report_code}: {upload_id}',
                'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
                'category': 'cash_amount_above_extreme_threshold',
                'element': 'amount_local',
                'issue': f'CTR amount {amount} extreme value (EFT may be submitted as CTR)'
                })

                # Append upload id of the invalid report to a list for later usage (downloading XML reports)
                issues_upload_ids.append(upload_id)
                # Set the transaction as invalid
                is_txn_valid = False
        
            # Check if cash transaction amount is not a round amount (not multiples of 5 (change this to 10, 20, 100, etc. if necessary))
            if not (amount % 5 == 0):
                reporting_issues.append({
                'report_name': f'{report_code}: {upload_id}',
                'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
                'category': 'cash_amount_not_round_value',
                'element': 'amount_local',
                'issue': f'CTR amount: {amount} not round amount (may be EFT?)'
                })

                # Append upload id of the invalid report to a list for later usage (downloading XML reports)
                issues_upload_ids.append(upload_id)
                # Set the transaction as invalid
                is_txn_valid = False
    
    # Check if both sides of a cash transaction are accounts
    if report_code == 'CTR':
        if is_accounts_both_side(transaction):
            reporting_issues.append({
            'report_name': f'{report_code}: {upload_id}',
            'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
            'category': 'cash_transaction_both_From_and_To_sides_are_accounts',
            'element': 'transaction',
            'issue': 'cash transaction both From and To sides are accounts'
            })
            
            # Append upload id of the invalid report to a list for later usage (downloading XML reports)
            issues_upload_ids.append(upload_id)
            # Set the transaction as invalid
            is_txn_valid = False

    # Check if any side of a EFT transaction is account
    if report_code == 'EFT':
        if not is_accounts_any_side(transaction):
            reporting_issues.append({
            'report_name': f'{report_code}: {upload_id}',
            'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
            'category': 'EFT_transaction_any_of_From_and_To_side_is_not_account',
            'element': 'transaction',
            'issue': 'EFT transaction any of From and To side is not account'
            })
            
            # Append upload id of the invalid report to a list for later usage (downloading XML reports)
            issues_upload_ids.append(upload_id)
            # Set the transaction as invalid
            is_txn_valid = False

    # Check if both side of an IFT transaction country is 'LK'
    if report_code == 'IFT':
        if is_both_sides_LK(transaction):
            reporting_issues.append({
            'report_name': f'{report_code}: {upload_id}',
            'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
            'category': 'IFT_transaction_both_From_and_To_side_countries_are_LK',
            'element': 'transaction',
            'issue': 'IFT transaction both From and To side countries are LK'
            }) 
            
            # Append upload id of the invalid report to a list for later usage (downloading XML reports)
            issues_upload_ids.append(upload_id)
            # Set the transaction as invalid
            is_txn_valid = False


    # ****************************** FROM SIDE ***************************************
    # ********************************************************************************

    # <from_my_client> ----------------------------------------
    from_my_client = transaction.find('t_from_my_client')
    if from_my_client is not None:
        from_funds_code = from_my_client.find('from_funds_code')
        from_country = from_my_client.find('from_country')
        
        # Invalid if CTR report has from country not LK
        if (report_code == 'CTR') & (from_country.text != 'LK'):
            reporting_issues.append({
            'report_name': f'{report_code}: {upload_id}',
            'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
            'category': 'cash_transaction_From_country_not_LK',
            'element': 'from_my_client_country',
            'issue': f'cash transaction From country: {from_country.text} not LK'
            })
            
            # Append upload id of the invalid report to a list for later usage (downloading XML reports)
            issues_upload_ids.append(upload_id)
            # Set the transaction as invalid
            is_txn_valid = False

        # 1. <from my client Persons>
        from_person = from_my_client.find('from_person')
        if from_person is not None:
            # Validate person
            validation_result = validate_person(person=from_person, client_type='my_client', transmode=transmode_code)
            if validation_result != 'valid':
                reporting_issues.append({
                'report_name': f'{report_code}: {upload_id}',
                'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
                'category': 'invalid_person_details',
                'element': 'from_my_client_person',
                'issue': validation_result
                 })
                
                # Append upload id of the invalid report to a list for later usage (downloading XML reports)
                issues_upload_ids.append(upload_id)
                # Set the transaction as invalid
                is_txn_valid = False

        # 2. <from my client Entities>
        from_entity = from_my_client.find('from_entity')
        if from_entity is not None:
            # Vlidate entity
            validation_result = validate_entity(entity=from_entity, is_my_client=True)
            if validation_result != 'valid':
                reporting_issues.append({
                'report_name': f'{report_code}: {upload_id}',
                'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
                'category': 'invalid_entity_details',
                'element': 'from_my_client_entity',
                'issue': validation_result
                 })
                
                # Append upload id of the invalid report to a list for later usage (downloading XML reports)
                issues_upload_ids.append(upload_id)
                # Set the transaction as invalid
                is_txn_valid = False

        # 3. <from my client Accounts>
        from_account = from_my_client.find('from_account')
        if from_account is not None:
            # Validate account
            validation_result = validate_account(report_code, account=from_account, is_my_client=True, rentity_id=report_entity_id)
            if validation_result != 'valid':
                reporting_issues.append({
                'report_name': f'{report_code}: {upload_id}',
                'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
                'category': 'invalid_account_details',
                'element': 'from_my_client_account',
                'issue': validation_result
                 })
                
                # Append upload id of the invalid report to a list for later usage (downloading XML reports)
                issues_upload_ids.append(upload_id)
                # Set the transaction as invalid
                is_txn_valid = False

            # Check if account number is equal to the amount
            account = from_account.find('account')
            account_number = get_numeric_value(account)
            if account_number is not None and account_number == amount:
                reporting_issues.append({
                'report_name': f'{report_code}: {upload_id}',
                'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
                'category': 'amount_equal_to_account_number',
                'element': 'from_my_client_account',
                'issue': f'amount: {amount} equal to account number'
                 })
                
                # Append upload id of the invalid report to a list for later usage (downloading XML reports)
                issues_upload_ids.append(upload_id)
                # Set the transaction as invalid
                is_txn_valid = False

    # <from not my client> ----------------------------------------
    from_client = transaction.find('t_from')
    if from_client is not None:
        from_funds_code = from_client.find('from_funds_code')
        from_country = from_client.find('from_country')
        # Invalid if CTR report has from country not LK
        if (report_code == 'CTR') & (from_country.text != 'LK'):
            reporting_issues.append({
            'report_name': f'{report_code}: {upload_id}',
            'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
            'category': 'cash_transaction_From_country_not_LK',
            'element': 'from_country',
            'issue': f'cash transaction From country: {from_country.text} not LK'
            })
            
            # Append upload id of the invalid report to a list for later usage (downloading XML reports)
            issues_upload_ids.append(upload_id)
            # Set the transaction as invalid
            is_txn_valid = False

        # 1. <from not my client persons>
        from_person = from_client.find('from_person')
        if from_person is not None:
            # Validate person
            validation_result = validate_person(person=from_person, client_type='not_my_client', transmode=transmode_code)
            if validation_result != 'valid':
                reporting_issues.append({
                'report_name': f'{report_code}: {upload_id}',
                'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
                'category': 'invalid_person_details',
                'element': 'from_person',    
                'issue': validation_result
                 })
                
                # Append upload id of the invalid report to a list for later usage (downloading XML reports)
                issues_upload_ids.append(upload_id)
                # Set the transaction as invalid
                is_txn_valid = False

        # 2. <from not my client Entities>
        from_entity = from_client.find('from_entity')
        if from_entity is not None:
            # Validate entity
            validation_result = validate_entity(entity=from_entity, is_my_client=False)
            if validation_result != 'valid':
                reporting_issues.append({
                'report_name': f'{report_code}: {upload_id}',
                'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
                'category': 'invalid_entity_details',
                'element': 'from_entity',
                'issue': validation_result
                 })
                
                # Append upload id of the invalid report to a list for later usage (downloading XML reports)
                issues_upload_ids.append(upload_id)
                # Set the transaction as invalid
                is_txn_valid = False

        # 3. <from not my client Accounts>
        from_account = from_client.find('from_account')
        if from_account is not None:
            # Validate account
            validation_result = validate_account(report_code, account=from_account, is_my_client=False, rentity_id=report_entity_id)
            if validation_result != 'valid':
                reporting_issues.append({
                'report_name': f'{report_code}: {upload_id}',
                'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
                'category': 'invalid_account_details',
                'element': 'from_account',
                'issue': validation_result
                 })
                
                # Append upload id of the invalid report to a list for later usage (downloading XML reports)
                issues_upload_ids.append(upload_id)
                # Set the transaction as invalid
                is_txn_valid = False
                
            # Check if account number is equal to the amount
            account = from_account.find('account')
            account_number = get_numeric_value(account)
            if account_number is not None and account_number == amount:
                reporting_issues.append({
                'report_name': f'{report_code}: {upload_id}',
                'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
                'category': 'amount_equal_to_account_number',
                'element': 'from_account',
                'issue': f'amount: {amount} equal to account number'
                 })
                
                # Append upload id of the invalid report to a list for later usage (downloading XML reports)
                issues_upload_ids.append(upload_id)
                # Set the transaction as invalid
                is_txn_valid = False

    # ------------------------------------------------------------------


    # ****************************** TO SIDE ***************************************
    # ********************************************************************************

    # <to_my_client> ----------------------------------------
    to_my_client = transaction.find('t_to_my_client')
    if to_my_client is not None:
        to_funds_code = to_my_client.find('to_funds_code')
        to_country = to_my_client.find('to_country')
        # Invalid if CTR report has To Country not LK
        if (report_code == 'CTR') & (to_country.text != 'LK'):
            reporting_issues.append({
            'report_name': f'{report_code}: {upload_id}',
            'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
            'category': 'cash_transaction_To_country_not_LK',
            'element': 'to_my_client_country',
            'issue': f'cash transaction To country: {to_country.text} not LK'
            })
            
            # Append upload id of the invalid report to a list for later usage (downloading XML reports)
            issues_upload_ids.append(upload_id)
            # Set the transaction as invalid
            is_txn_valid = False

        # 1. <to my client persons>
        to_person = to_my_client.find('to_person')
        if to_person is not None:
            # Validate person
            validation_result = validate_person(person=to_person, client_type='my_client', transmode=transmode_code)
            if validation_result != 'valid':
                reporting_issues.append({
                'report_name': f'{report_code}: {upload_id}',
                'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
                'category': 'invalid_person_details',
                'element': 'to_my_client_person',
                'issue': validation_result
                 })
                
                # Append upload id of the invalid report to a list for later usage (downloading XML reports)
                issues_upload_ids.append(upload_id)
                # Set the transaction as invalid
                is_txn_valid = False

        # 2. <to my client Entities>
        to_entity = to_my_client.find('to_entity')
        if to_entity is not None:
            # Validate entity
            validation_result = validate_entity(entity=to_entity, is_my_client=True)
            if validation_result != 'valid':
                reporting_issues.append({
                'report_name': f'{report_code}: {upload_id}',
                'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
                'category': 'invalid_entity_details',
                'element': 'to_my_client_entity',
                'issue': validation_result
                 })
                
                # Append upload id of the invalid report to a list for later usage (downloading XML reports)
                issues_upload_ids.append(upload_id)
                # Set the transaction as invalid
                is_txn_valid = False

        # 3. <to my client Accounts>
        to_account = to_my_client.find('to_account')
        if to_account is not None:
            # Validate account
            validation_result = validate_account(report_code, account=to_account, is_my_client=True, rentity_id=report_entity_id)
            if validation_result != 'valid':
                reporting_issues.append({
                'report_name': f'{report_code}: {upload_id}',
                'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
                'category': 'invalid_account_details',
                'element': 'to_my_client_account',
                'issue': validation_result
                 })
                
                # Append upload id of the invalid report to a list for later usage (downloading XML reports)
                issues_upload_ids.append(upload_id)
                # Set the transaction as invalid
                is_txn_valid = False
                
            # Check if account number is equal to the amount
            account = to_account.find('account')
            account_number = get_numeric_value(account)
            if account_number is not None and account_number == amount:
                reporting_issues.append({
                'report_name': f'{report_code}: {upload_id}',
                'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
                'category': 'amount_equal_to_account_number',
                'element': 'to_my_client_account',
                'issue': f'amount: {amount} equal to account number'
                 })
                
                # Append upload id of the invalid report to a list for later usage (downloading XML reports)
                issues_upload_ids.append(upload_id)
                # Set the transaction as invalid
                is_txn_valid = False
    # ------------------------------------------------------------------

    # <to_not_my_client> ----------------------------------------
    to_client = transaction.find('t_to')
    if to_client is not None:
        to_funds_code = to_client.find('to_funds_code')
        to_country = to_client.find('to_country')
        # Invalid if CTR report has to country not LK
        if (report_code == 'CTR') & (to_country.text != 'LK'):
            reporting_issues.append({
            'report_name': f'{report_code}: {upload_id}',
            'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
            'category': 'cash_transaction_To_country_not_LK',
            'element': 'to_country',
            'issue': f'cash transaction To country: {to_country.text} not LK'
            })
            
            # Append upload id of the invalid report to a list for later usage (downloading XML reports)
            issues_upload_ids.append(upload_id)
            # Set the transaction as invalid
            is_txn_valid = False

        # 1. <to not my client persons>
        to_person = to_client.find('to_person')
        if to_person is not None:
            # Validate person
            validation_result = validate_person(person=to_person, client_type='not_my_client', transmode=transmode_code)
            if validation_result != 'valid':
                reporting_issues.append({
                'report_name': f'{report_code}: {upload_id}',
                'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
                'category': 'invalid_person_details',
                'element': 'to_person',
                'issue': validation_result
                 })
                
                # Append upload id of the invalid report to a list for later usage (downloading XML reports)
                issues_upload_ids.append(upload_id)
                # Set the transaction as invalid
                is_txn_valid = False

        # 2. <to not my client Entities>
        to_entity = to_client.find('to_entity')
        if to_entity is not None:
            # Validate entity
            validation_result = validate_entity(entity=to_entity, is_my_client=False)
            if validation_result != 'valid':
                reporting_issues.append({
                'report_name': f'{report_code}: {upload_id}',
                'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
                'category': 'invalid_entity_details',
                'element': 'to_entity',
                'issue': validation_result
                 })
                
                # Append upload id of the invalid report to a list for later usage (downloading XML reports)
                issues_upload_ids.append(upload_id)
                # Set the transaction as invalid
                is_txn_valid = False

        # 3. <to not my client Accounts>
        to_account = to_client.find('to_account')
        if to_account is not None:
            # Validate account
            validation_result = validate_account(report_code, account=to_account, is_my_client=False, rentity_id=report_entity_id)
            if validation_result != 'valid':
                reporting_issues.append({
                'report_name': f'{report_code}: {upload_id}',
                'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
                'category': 'invalid_account_details',
                'element': 'to_account',
                'issue': validation_result
                 })
                
                # Append upload id of the invalid report to a list for later usage (downloading XML reports)
                issues_upload_ids.append(upload_id)
                # Set the transaction as invalid
                is_txn_valid = False
                
            # Check if account number is equal to the amount
            account = to_account.find('account')
            account_number = get_numeric_value(account)
            if account_number is not None and account_number == amount:
                reporting_issues.append({
                'report_name': f'{report_code}: {upload_id}',
                'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
                'category': 'amount_equal_to_account_number',
                'element': 'to_account',
                'issue': f'amount: {amount} equal to account number'
                 })
                
                # Append upload id of the invalid report to a list for later usage (downloading XML reports)
                issues_upload_ids.append(upload_id)
                # Set the transaction as invalid
                is_txn_valid = False
    # ------------------------------------------------------------------


    # ****************************** MULTI PARTY ***************************************
    # ********************************************************************************

    # <involved_parties> ----------------------------------------
    involved_parties = transaction.find('involved_parties')
    if involved_parties is not None:
        party = involved_parties.find('party')
        if party is not None:
            party_role = party.find('role').text
            party_funds_code = party.find('funds_code').text
            party_country = party.find('country').text

            # 1. <multi party Persons>
            multi_person = party.find('person_my_client')
            if multi_person is not None:
                # Validate person
                validation_result = validate_person(person=multi_person, client_type='my_client', transmode=transmode_code)
                if validation_result != 'valid':
                    reporting_issues.append({
                    'report_name': f'{report_code}: {upload_id}',
                    'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
                    'category': 'invalid_person_details',
                    'element': 'multi_person',
                    'issue': validation_result
                     })
                    
                    # Append upload id of the invalid report to a list for later usage (downloading XML reports)
                    issues_upload_ids.append(upload_id)
                    # Set the transaction as invalid
                    is_txn_valid = False

            # 2. <multi party Entities>
            multi_entity = party.find('entity_my_client')
            if multi_entity is not None:
                # Validate entity
                validation_result = validate_entity(entity=multi_entity, is_my_client=True)
                if validation_result != 'valid':
                    reporting_issues.append({
                    'report_name': f'{report_code}: {upload_id}',
                    'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
                    'category': 'invalid_entity_details',
                    'element': 'multi_entity',
                    'issue': validation_result
                     })
                    
                    # Append upload id of the invalid report to a list for later usage (downloading XML reports)
                    issues_upload_ids.append(upload_id)
                    # Set the transaction as invalid
                    is_txn_valid = False

            # 3. <multi party Accounts>
            multi_account = party.find('account_my_client')
            if multi_account is not None:
                # Validate account
                validation_result = validate_account(report_code, account=multi_account, is_my_client=True, rentity_id=report_entity_id)
                if validation_result != 'valid':
                    reporting_issues.append({
                    'report_name': f'{report_code}: {upload_id}',
                    'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
                    'category': 'invalid_account_details',
                    'element': 'multi_account',
                    'issue': validation_result
                     }) 
                    
                    # Append upload id of the invalid report to a list for later usage (downloading XML reports)
                    issues_upload_ids.append(upload_id)
                    # Set the transaction as invalid
                    is_txn_valid = False
                    
                # Check if account number is equal to the amount
                account = multi_account.find('account')
                account_number = get_numeric_value(account)
                if account_number is not None and account_number == amount:
                    reporting_issues.append({
                    'report_name': f'{report_code}: {upload_id}',
                    'transaction_number': transaction_number.text if transaction_number is not None else f'<transaction> {transaction_seq}',
                    'category': 'amount_equal_to_account_number',
                    'element': 'multi_account',
                    'issue': f'amount: {amount} equal to account number'
                     })

                    # Append upload id of the invalid report to a list for later usage (downloading XML reports)
                    issues_upload_ids.append(upload_id)
                    # Set the transaction as invalid
                    is_txn_valid = False
    # ------------------------------------------------------------------
    
    return is_txn_valid
# Function to validate XML report 

# Uses iterparse to process XML content in a memroy-friendly way, clearing each element after processing 

def process_report(xml_content, upload_id):
    global details
    try:
        # Variable to count invalid transactions
        invalid_txn_count = 0
        
        # Convert the XML string to a file-like object for iterparse (faster processing and memory efficient)
        xml_file_like_object = io.StringIO(xml_content)

        # Assume reporting_issues is accessible and defined elsewhere
        global reporting_issues

        # Defining these variables here so they are visible to 'transaction' <<if block>>
        report_code = ''
        submission_date_text = ''
        submission_date = ''
        transaction_seq = 0

        # Loop through the XML content as stream
        for event, elem in ET.iterparse(xml_file_like_object, events=('start', 'end')):
            if event == 'start':
                # Handle start of xml elements in stream if needed (e.g., initializing something)
                pass

            if event == 'end':
                # Process xml elements as they are closed, reducing memory usage
                if elem.tag == 'report_code':
                    report_code = elem.text if elem.text is not None else None
                    elem.clear()  # Clear the processed element to free memory
                    if report_code not in report_types:
                        return False, 0

                if elem.tag == 'submission_date':
                    submission_date_text = elem.text if elem.text is not None else None
                    submission_date = parse_date(submission_date_text)
                    elem.clear()  # Clear the processed element to free memory

                if elem.tag == 'transaction':
                    # Process each <transaction> element
                    transaction_seq += 1
                    txn_valid =  process_transaction(transaction_seq, elem, report_code, upload_id, submission_date)
                    # If transaction is not valid after validation, increment the counter
                    if not txn_valid:
                        invalid_txn_count += 1
                    elem.clear()  # Clear the processed element to free memory

        # Clear the root element to free up memory
        elem.clear()
        return True, invalid_txn_count
    
    except Exception as e:
        exc_type, exc_obj, tb = traceback.sys.exc_info()
        f = tb.tb_frame
        lineno = tb.tb_lineno
        filename = f.f_code.co_filename
        linecache.checkcache(filename)
        line = linecache.getline(filename, lineno, f.f_globals)
        
        # Capture the current traceback, format it to a string, and then print it
        traceback_details = traceback.format_exc()
        details += f'\033[31mError in processing report id: {upload_id}\033[0m [Error: {str(e)}]\nOn line {lineno}: {line.strip()}\n'
        details += f'Check transaction sequence no: {transaction_seq} in XML file\n'


# Function to validate XML reports submitted by a Reporting Entity (RE)

# This function validates all XML files in the specified local folder 
# by passing them to function 'process_report(xml_content, report_id)'.
# It keeps track of memory usage after validating each XML file, and breaks the loop if it exceeds predefined threshold
# in config file to prevent out of memory issues. After validating all XML files, this function processes the
# lists of validation issues and uploa_ids of relevant XML files, and saves them to files for later usage. It also cleans
# memory after validating each XML file for efficient memory management

def validate_reporting_entity_local(report_entity_name, report_entity_id, report_entity_swift, xml_folder_path):
    global details
    # Initialize xml_reports at the start of the function
    xml_reports = 0
    invalid_transaction_count = 0

    try:
        details += f''
        details += f'Obtaining XML files for {report_entity_name} RE ID: {report_entity_id}  SWIFT: {report_entity_swift}\n'

        # Obtain list of XML files in the specified folder
        xml_file_list = glob.glob(os.path.join(xml_folder_path, '*.xml'))
        details += f"Total XML files: {len(xml_file_list)}\n"

        for xml_file_path in tqdm(xml_file_list, desc='Validating XML Reports '):
            try:
                # Read the XML content from the file
                with open(xml_file_path, 'r') as xml_file:
                    xml_content = xml_file.read()

                # Extract report_id from the file name (assuming the report_id is part of the file name)
                report_id = os.path.basename(xml_file_path).split('.')[0]

                # Process the fetched XML content
                validated, invalid_txn_report = process_report(xml_content, report_id)
                if validated:
                    xml_reports += 1
                    # Add the invalid transactions count of the report to the total count
                    invalid_transaction_count += invalid_txn_report

                # Explicitly delete the large object
                del xml_content

                memory_usage_current = memory_usage()
                if memory_usage_current > memory_threshold_break:
                    details += f'Memory usage: {memory_usage_current} MB. Breaking loop to prevent out of memory error\n'
                    gc.collect()  # Manually trigger garbage collection
                    break
                elif memory_usage_current > memory_threshold_clean:
                    gc.collect()  # Manually trigger garbage collection

            except Exception as e:
                # Capture the current traceback, format it to a string, and then print it
                traceback_details = traceback.format_exc()
                details += f'Error in processing report id: {report_id}Error: {str(e)}]\nTraceback details:\n{traceback_details}\n'
                continue

        # Convert issues lists to dataframes and write them to Excel files. If rows exceed 900,000 (Excel max), write only top 900,000 records
        df_reporting_issues = pd.DataFrame(reporting_issues)
        df_issues_upload_ids = pd.DataFrame(issues_upload_ids)
        global output_path
        if not df_reporting_issues.empty:
            details += f'There are issues in the XML Reports  !!!\n'
            #output_directory = 'validation_results'
            if not os.path.exists(output_path):
                os.makedirs(output_path)
                
            # Apply the function to each element in the 'issue' column
            df_reporting_issues['issue'] = df_reporting_issues['issue'].apply(parse_list)

            # Handle NaN values: convert them to empty lists
            df_reporting_issues['issue'] = df_reporting_issues['issue'].apply(lambda x: x if isinstance(x, list) else [])

            # Now the 'issue' column can be safely exploded
            df_reporting_issues = df_reporting_issues.explode('issue')
            timestamp = datetime.now().strftime('%Y-%m-%d_%H-%M')

            # If error records are more than Excel can handle, save as CVS file and save top portion to Excel
            if df_reporting_issues.shape[0] > max_rows_excel:
                details += f'There are {df_reporting_issues.shape[0]} issues. Limiting to 900,000 reporting issues for saving to Excel file ...\n'
                issues_file_name = f'{output_path}/report_issues_all_[{report_entity_name}_{report_entity_id}].csv'
                df_reporting_issues.to_csv(issues_file_name, index=False)
                df_reporting_issues.head(max_rows_excel).to_excel(f'{output_path}/report_issues_part_[{report_entity_name}_{report_entity_id}].xlsx', index=False, engine='openpyxl')
                details += f'Reporting issues were saved to file: {issues_file_name}\n'
            
            else:
                issues_file_name = f'{output_path}/report_issues_[{report_entity_name}_{report_entity_id}].xlsx'
                df_reporting_issues.to_excel(issues_file_name, index=False, engine='openpyxl')
                details += f'Reporting issues were saved to file: {issues_file_name}\n'
        else:
            details += f'Reporting issues were not found !!!\n'
                
        if not df_issues_upload_ids.empty:
            # Remove the duplicates of the dataframe and save to file for later usage (download XML reports)
            df_issues_upload_ids.drop_duplicates(inplace=True)
            df_issues_upload_ids.to_csv(f'{output_path}/{report_entity_name}_upload_ids.csv', index=False)
        
        if xml_reports > 0:
            details += f'Total of {xml_reports} XML files have been processed.'
            details += f'There are {len(df_reporting_issues)} issues in {len(df_issues_upload_ids)} reports to be rectified\n'
            details += f'Total flagged transactions: {invalid_transaction_count}\n'
            
        else:
            details += f'No files were validated'
        
        details += f'Memory Usage: {memory_usage():.2f} MB\n'
        details += f'---------------------------------------------------------------------'
        
    except Exception as e:
        details += f'Error in executing script for {report_entity_name} [Error: {str(e)}]\n'

class Window(QMainWindow):
    def __init__(self):
        super().__init__()

        self.setGeometry(500, 500, 500, 400)
        self.setWindowTitle("GOAML Tool")

        # Create central widget and layout
        self.central_widget = QWidget()
        self.setCentralWidget(self.central_widget)
        self.layout = QVBoxLayout()

        # Input Folder Label and Button
        self.input_label = QLabel("Input Folder: None")
        self.layout.addWidget(self.input_label)

        self.input_button = QPushButton("Select Input Folder")
        self.input_button.clicked.connect(self.select_input_folder)
        self.layout.addWidget(self.input_button)

        # Output Folder Label and Button
        self.output_label = QLabel("Output Folder: None")
        self.layout.addWidget(self.output_label)

        self.output_button = QPushButton("Select Output Folder")
        self.output_button.clicked.connect(self.select_output_folder)
        self.layout.addWidget(self.output_button)

        # Validate Button
        self.validate_button = QPushButton("Validate Configuration")
        self.validate_button.clicked.connect(self.validateButton)
        self.layout.addWidget(self.validate_button)

        # Output Details Label
        self.output_details_label = QLabel("")
        self.layout.addWidget(self.output_details_label)

        self.central_widget.setLayout(self.layout)



          # Dictionary to hold swift codes and institution names, which is used in the function to check if a given swift code for an account institution matches its institution name
   

    # Method to select input folder
    def select_input_folder(self):
        global local_folder_path
        folder = QFileDialog.getExistingDirectory(self, "Select Input Folder")
     
        if folder:
            self.input_label.setText(f"Input Folder: {folder}")
            local_folder_path=folder

   
    # Method to select output folder
    def select_output_folder(self):
        global output_path
    
        folder = QFileDialog.getExistingDirectory(self, "Select Output Folder")
        if folder:
            self.output_label.setText(f"Output Folder: {folder}")
            output_path=folder
            

    # Method to validate the configuration
    def validateButton(self):
        global details
        details = "Configuration Parameters:\n"
        details += f"reporting_window = {reporting_window}\n"
        details += f"report_start_date = {report_start_date}\n"
        details += f"report_end_date = {report_end_date}\n"
        details += f"ctr_threshold = {ctr_threshold}\n"
        details += f"report_types = {report_types}\n"
        details += f"incorp_number_reg_types = {incorp_number_reg_types}\n"
        details += f"invalid_acc_prefixes = {invalid_acc_prefixes}\n"
        details += f"invalid_acc_chars = {invalid_acc_chars}\n"
        details += f"swift_name_match_threshold = {swift_name_match_threshold}\n"
        details += f"check_late_submissions = {check_late_submissions}\n"
        details += f"input = {local_folder_path}\n"
        details += f"output = {output_path}\n"
        details += f"----------------------------------------------------------------------------\n"
        try: 
           details +=f'Validating Reports of {report_entity_name} (rentity_id: {report_entity_id}, SWIFT: {report_entity_swift})\n'
           details +='---------------------------------------------------------------------\n'
   
  
           validate_reporting_entity_local(report_entity_name, report_entity_id, report_entity_swift, local_folder_path)

           details +='\n'
           details +='All reports have been processed.\n'
           self.output_details_label.setText(details)
           # Clean memory
           gc.collect()

        except Exception as e:
           details += f'Error in executing script for {report_entity_name} [Error: {str(e)}]\n'
           # Clean memory
           gc.collect()

        # Display the details in the output details label
        
        


def main():
    app = QApplication(sys.argv)
    win = Window()
    win.show()
    sys.exit(app.exec_())

if __name__ == "__main__":
    main()