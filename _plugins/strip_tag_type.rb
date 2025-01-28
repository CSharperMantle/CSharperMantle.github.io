module Jekyll
  module StripTagTypeFilter
    def strip_tag_type(input)
      (!input.nil? && input.kind_of?(String)) ? input.sub(/^[^:]+:/, '') : input
    end
    def strip_tag_type_each(input)
      (!input.nil? && input.kind_of?(Array)) ? input.map { |tag| tag.sub(/^[^:]+:/, '') } : []
    end
  end
end

Liquid::Template.register_filter(Jekyll::StripTagTypeFilter)
