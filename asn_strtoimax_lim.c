    enum asn_strtox_result_e
    asn_strtoimax_lim(const char *str, const char **end, intmax_t *intp) {
	int sign = 1;
	intmax_t value;

	const intmax_t asn1_intmax_max = ((~(uintmax_t)0) >> 1);
	const intmax_t upper_boundary = asn1_intmax_max / 10;
	intmax_t last_digit_max = asn1_intmax_max % 10;

	if(str >= *end) return ASN_STRTOX_ERROR_INVAL;

	switch(*str) {
	case '-':
	    last_digit_max++;
	    sign = -1;
	    /* FALL THROUGH */
	case '+':
	    str++;
	    if(str >= *end) {
		*end = str;
		return ASN_STRTOX_EXPECT_MORE; }
	}

	for(value = 0; str < (*end); str++) {
	    if(*str >= 0x30 && *str <= 0x39) {
		int d = *str - '0';
		if(value < upper_boundary) {
		    value = value * 10 + d;
		} else if(value == upper_boundary) {
		    if(d <= last_digit_max) {
			if(sign > 0) {
			    value = value * 10 + d;
			} else {
			    sign = 1;
			    value = -value * 10 - d;
			}
			str += 1;
			if(str < *end) {
			    // If digits continue, we're guaranteed out of range.
			    *end = str;
			    if(*str >= 0x30 && *str <= 0x39) {
				return ASN_STRTOX_ERROR_RANGE;
			    } else {
				*intp = sign * value;
				return ASN_STRTOX_EXTRA_DATA;
			    }
			}
			break;
		    } else {
			*end = str;
			return ASN_STRTOX_ERROR_RANGE;
		    }
		} else {
		    *end = str;
		    return ASN_STRTOX_ERROR_RANGE;
		}
	    } else {
		*end = str;
		*intp = sign * value;
		return ASN_STRTOX_EXTRA_DATA;
	    }
	}

	*end = str;
	*intp = sign * value;
	return ASN_STRTOX_OK; }
