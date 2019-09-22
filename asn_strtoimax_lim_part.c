for(value = 0; str < (*end); str++) {
    if(*str >= 0x30 && *str <= 0x39) {
        int d = *str - '0';
        if(value < upper_boundary) {
            value = value * 10 + d;
        } else if(value == upper_boundary) {
            if(d <= last_digit_max) {
                if(sign > 0) { value = value * 10 + d;
                } else { sign = 1;
                    value = -value * 10 - d; }
                str += 1;
                if(str < *end) {
                    // If digits continue, we're guaranteed out of range.
                    *end = str;
                    if(*str >= 0x30 && *str <= 0x39) { return ASN_STRTOX_ERROR_RANGE;
                    } else { *intp = sign * value;
                        return ASN_STRTOX_EXTRA_DATA; }}
                break;
            } else { *end = str;
                return ASN_STRTOX_ERROR_RANGE; }
        } else { *end = str;
            return ASN_STRTOX_ERROR_RANGE; }
    } else { *end = str;
        *intp = sign * value;
        return ASN_STRTOX_EXTRA_DATA; }}
*end = str;
*intp = sign * value;
return ASN_STRTOX_OK; }
