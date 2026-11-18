#pragma once

#include <array>
#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <ostream>
#include <stdexcept>
#include <utility>
#include <algebra/finite_fields/modulus.hpp>

namespace algebra {

template<std::uint32_t P, std::size_t K = 1, class ModulusPolicy = FirstEnumeratedIrreducible>
class FiniteField;

template<std::uint32_t P, std::size_t K, class ModulusPolicy>
class UncachedFiniteFieldElement : public AdditiveOperators<UncachedFiniteFieldElement<P, K, ModulusPolicy>>,
                           public MultiplicativeOperators<UncachedFiniteFieldElement<P, K, ModulusPolicy>>,
                           public DivisionOperators<UncachedFiniteFieldElement<P, K, ModulusPolicy>> {
    static_assert(is_prime(P));
    static_assert(K > 0);

public:
    using parent_type = FiniteField<P, K, ModulusPolicy>;
    using algebra = FieldDescriptor;
    using coefficient_type = PrimeFieldElement<P>;
    using polynomial_type = Polynomial<coefficient_type>;

private:
    polynomial_type value_;
    struct Reduced {};

    UncachedFiniteFieldElement(polynomial_type value, Reduced) : value_(std::move(value)) {}

public:
    UncachedFiniteFieldElement() {
        static_cast<void>(parent_type::modulus());
    }

    static UncachedFiniteFieldElement from_polynomial(const polynomial_type& value) {
        polynomial_type remainder = value % parent_type::modulus();
        return UncachedFiniteFieldElement(std::move(remainder), Reduced{});
    }

    static UncachedFiniteFieldElement from_coefficients(std::initializer_list<std::int64_t> values) {
        polynomial_type value;
        std::size_t index = 0;
        for (const auto coefficient : values) {
            value.set_coefficient(index++, coefficient_type::from_integer(coefficient));
        }
        return from_polynomial(value);
    }

    static UncachedFiniteFieldElement from_integer(std::int64_t value) {
        return from_polynomial(polynomial_type{coefficient_type::from_integer(value)});
    }

    static UncachedFiniteFieldElement from_index(std::uint64_t index) {
        if (index >= parent_type::cardinality()) {
            throw std::out_of_range("Finite field element index is out of range");
        }
        polynomial_type value;
        for (std::size_t i = 0; i < K; ++i) {
            value.set_coefficient(i, coefficient_type::from_index(index % P));
            index /= P;
        }
        return from_polynomial(value);
    }

    static UncachedFiniteFieldElement zero() {
        return UncachedFiniteFieldElement{};
    }

    static UncachedFiniteFieldElement one() {
        return from_integer(1);
    }

    UncachedFiniteFieldElement add(const UncachedFiniteFieldElement& other) const {
        const polynomial_type sum = value_.add(other.value_);
        return from_polynomial(sum);
    }

    UncachedFiniteFieldElement negate() const {
        return from_polynomial(value_.negate());
    }

    UncachedFiniteFieldElement multiply(const UncachedFiniteFieldElement& other) const {
        const polynomial_type product = value_.multiply(other.value_);
        return from_polynomial(product);
    }

    UncachedFiniteFieldElement reciprocal() const {
        if (is_zero()) {
            throw std::domain_error("Zero has no reciprocal");
        }
        polynomial_type previous_remainder = parent_type::modulus();
        polynomial_type remainder = value_;
        polynomial_type previous_coefficient = polynomial_type::zero();
        polynomial_type coefficient = polynomial_type::one();
        while (!remainder.is_zero()) {
            auto division = previous_remainder.divmod(remainder);
            polynomial_type next_remainder = std::move(division.second);
            polynomial_type next_coefficient =
                previous_coefficient - division.first.multiply(coefficient);
            previous_remainder = std::move(remainder);
            remainder = std::move(next_remainder);
            previous_coefficient = std::move(coefficient);
            coefficient = std::move(next_coefficient);
        }
        if (previous_remainder.degree() != 0) {
            throw std::logic_error("The element is not invertible for this modulus");
        }
        const coefficient_type scale = previous_remainder.coefficient(0).reciprocal();
        return from_polynomial(previous_coefficient.scale_left(scale));
    }

    bool is_zero() const {
        return value_.is_zero();
    }

    bool is_one() const {
        return value_.is_one();
    }

    coefficient_type coefficient(std::size_t index) const {
        if (index >= K) {
            throw std::out_of_range("Finite field coefficient index is out of range");
        }
        return value_.coefficient(index);
    }

    std::array<coefficient_type, K> coefficients() const {
        std::array<coefficient_type, K> result{};
        for (std::size_t i = 0; i < K; ++i) {
            result[i] = value_.coefficient(i);
        }
        return result;
    }

    const polynomial_type& representative() const {
        return value_;
    }

    const parent_type& parent() const {
        static const parent_type instance;
        return instance;
    }

    bool operator==(const UncachedFiniteFieldElement& other) const {
        return value_ == other.value_;
    }

    friend std::ostream& operator<<(std::ostream& out, const UncachedFiniteFieldElement& value) {
        return out << value.value_;
    }
};

template<std::uint32_t P, std::size_t K, class ModulusPolicy>
class FiniteFieldElement : public AdditiveOperators<FiniteFieldElement<P, K, ModulusPolicy>>,
                           public MultiplicativeOperators<FiniteFieldElement<P, K, ModulusPolicy>>,
                           public DivisionOperators<FiniteFieldElement<P, K, ModulusPolicy>> {
    static_assert(is_prime(P));
    static_assert(K > 0);

public:
    using parent_type = FiniteField<P, K, ModulusPolicy>;
    using algebra = FieldDescriptor;
    using coefficient_type = PrimeFieldElement<P>;
    using polynomial_type = Polynomial<coefficient_type>;
    static uint64_t get_index(const polynomial_type& value) {
	uint64_t i = 0, p = 1;
	for (size_t deg = 0; deg < K; deg++) {
		i += value.coefficient(deg).representative() * p;
		p *= P;
	}
	return i;
    }
private:
    polynomial_type value_;
    uint64_t index_ = 0;
    struct Reduced {};


    FiniteFieldElement(polynomial_type value, Reduced) : value_(std::move(value)),
				  			 index_(get_index(value_)) {}
public:
    FiniteFieldElement() {
        static_cast<void>(parent_type::modulus());
    }

    static FiniteFieldElement from_polynomial(const polynomial_type& value) {
        polynomial_type remainder = value % parent_type::modulus();
        return FiniteFieldElement(std::move(remainder), Reduced{});
    }

    static FiniteFieldElement from_coefficients(std::initializer_list<std::int64_t> values) {
        polynomial_type value;
        std::size_t index = 0;
        for (const auto coefficient : values) {
            value.set_coefficient(index++, coefficient_type::from_integer(coefficient));
        }
        return from_polynomial(value);
    }

    static FiniteFieldElement from_integer(std::int64_t value) {
        return from_polynomial(polynomial_type{coefficient_type::from_integer(value)});
    }

    static FiniteFieldElement from_index(std::uint64_t index) {
        if (index >= parent_type::cardinality()) {
            throw std::out_of_range("Finite field element index is out of range");
        }
        polynomial_type value;
        for (std::size_t i = 0; i < K; ++i) {
            value.set_coefficient(i, coefficient_type::from_index(index % P));
            index /= P;
        }
        return from_polynomial(value);
    }

    static FiniteFieldElement zero() {
        return FiniteFieldElement{};
    }

    static FiniteFieldElement one() {
        return from_integer(1);
    }

    FiniteFieldElement add(const FiniteFieldElement& other) const {
	if (parent_type::acache_[index_ * parent_type::cardinality() + other.index_].has_value())
		return *parent_type::acache_[index_ * parent_type::cardinality() + other.index_];
	else if (parent_type::acache_[other.index_ * parent_type::cardinality() + index_].has_value())
		return *parent_type::acache_[other.index_ * parent_type::cardinality() + index_];
        
        const polynomial_type sum = value_.add(other.value_);
        FiniteFieldElement element = from_polynomial(sum);
	parent_type::acache_[index_ * parent_type::cardinality() + other.index_] = element;
	parent_type::acache_[other.index_ * parent_type::cardinality() + index_] = element;

	return element;
    }

    FiniteFieldElement negate() const {
	if (parent_type::ncache_[index_].has_value())
		return *parent_type::ncache_[index_];
        FiniteFieldElement element = from_polynomial(value_.negate());
	parent_type::ncache_[index_] = element;
	return element;
    }

    FiniteFieldElement multiply(const FiniteFieldElement& other) const {
	if (parent_type::mcache_[index_ * parent_type::cardinality() + other.index_].has_value())
		return *parent_type::mcache_[index_ * parent_type::cardinality() + other.index_];
	else if (parent_type::mcache_[other.index_ * parent_type::cardinality() + index_].has_value())
		return *parent_type::mcache_[other.index_ * parent_type::cardinality() + index_];
        
	const polynomial_type product = value_.multiply(other.value_);
        FiniteFieldElement element = from_polynomial(product);
	parent_type::mcache_[index_ * parent_type::cardinality() + other.index_] = element;
	parent_type::mcache_[other.index_ * parent_type::cardinality() + index_] = element;
	return element;

    }

    FiniteFieldElement reciprocal() const {
        if (is_zero()) {
            throw std::domain_error("Zero has no reciprocal");
        }
	if (parent_type::rcache_[index_].has_value())
		return *parent_type::rcache_[index_];
        polynomial_type previous_remainder = parent_type::modulus();
        polynomial_type remainder = value_;
        polynomial_type previous_coefficient = polynomial_type::zero();
        polynomial_type coefficient = polynomial_type::one();
        while (!remainder.is_zero()) {
            auto division = previous_remainder.divmod(remainder);
            polynomial_type next_remainder = std::move(division.second);
            polynomial_type next_coefficient =
                previous_coefficient - division.first.multiply(coefficient);
            previous_remainder = std::move(remainder);
            remainder = std::move(next_remainder);
            previous_coefficient = std::move(coefficient);
            coefficient = std::move(next_coefficient);
        }
        if (previous_remainder.degree() != 0) {
            throw std::logic_error("The element is not invertible for this modulus");
        }
        const coefficient_type scale = previous_remainder.coefficient(0).reciprocal();
        FiniteFieldElement element = from_polynomial(previous_coefficient.scale_left(scale));
	parent_type::rcache_[index_] = element;
        return element;
    }

    bool is_zero() const {
        return value_.is_zero();
    }

    bool is_one() const {
        return value_.is_one();
    }

    coefficient_type coefficient(std::size_t index) const {
        if (index >= K) {
            throw std::out_of_range("Finite field coefficient index is out of range");
        }
        return value_.coefficient(index);
    }

    std::array<coefficient_type, K> coefficients() const {
        std::array<coefficient_type, K> result{};
        for (std::size_t i = 0; i < K; ++i) {
            result[i] = value_.coefficient(i);
        }
        return result;
    }

    const polynomial_type& representative() const {
        return value_;
    }

    const parent_type& parent() const {
        static const parent_type instance;
        return instance;
    }

    bool operator==(const FiniteFieldElement& other) const {
        return value_ == other.value_;
    }

    friend std::ostream& operator<<(std::ostream& out, const FiniteFieldElement& value) {
        return out << value.value_;
    }
};

template<std::uint32_t P, std::size_t K, class ModulusPolicy>
class FiniteField : public FieldStructure<FiniteFieldElement<P, K, ModulusPolicy>> {
    static_assert(is_prime(P));
    static_assert(K > 0);

public:
    using Element = FiniteFieldElement<P, K, ModulusPolicy>;
    using Base = PrimeField<Cyclic<P>>;
    using PolynomialType = typename Element::polynomial_type;
    static constexpr std::uint32_t characteristic = P;
    static constexpr std::size_t extension_degree = K;
    inline static std::vector<std::optional<Element>> mcache_ = [] {
		const uint64_t c = FiniteField<P, K>::cardinality();
		return std::vector<std::optional<Element>>(c * c, std::nullopt);
	}();
    inline static std::vector<std::optional<Element>> acache_ = [] {
		const uint64_t c = FiniteField<P, K>::cardinality();
		return std::vector<std::optional<Element>>(c * c, std::nullopt);
	}();
    inline static std::vector<std::optional<Element>> ncache_ = [] {
		const uint64_t c = FiniteField<P, K>::cardinality();
		return std::vector<std::optional<Element>>(c, std::nullopt);
	}();
    inline static std::vector<std::optional<Element>> rcache_ = [] {
		const uint64_t c = FiniteField<P, K>::cardinality();
		return std::vector<std::optional<Element>>(c, std::nullopt);
	}();

    FiniteField() {
        initialize();
    }

    static const PolynomialType& modulus() {
        static const PolynomialType value = [] {
            PolynomialType candidate = ModulusPolicy::template polynomial<P, K>();
            if (candidate.degree() != K || !candidate.leading_coefficient().is_one() ||
                !is_irreducible(candidate)) {
                throw std::invalid_argument("The modulus must be monic and irreducible with degree K");
            }
            return candidate;
        }();
        return value;
    }

    static void initialize() {
        static_cast<void>(modulus());
    }

    static std::uint64_t cardinality() {
        return checked_power(P, K);
    }

    static Element element(std::initializer_list<std::int64_t> values) {
	return Element::from_coefficients(values);
    }

    static Element element(std::int64_t value) {
	return Element::from_integer(value);
    }

    static Element zero() {
        return Element::zero();
    }

    static Element one() {
        return Element::one();
    }

    static Element alpha() {
        return Element::from_polynomial(PolynomialType::variable());
    }
};

}
